import Calderon.ActualCoarseUniformProductNorms
import Calderon.ActualCurrentCoefficientProductNormBounds
import Calderon.ActualUniformCoarseRestrictionSpectrum
import Calderon.ActualCrossSeriesQuantitativeNorm
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

theorem uniform_coarse_cross_series_with_uniform_amplitude (S : KnownSideSourceData) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ ∃ γ1 γ2 : ℝ, 0 < γ1 + γ2 - 1 ∧
    ∀ B s0 s1 : ℝ, 0 < B → 0 < s0 → s0 ≤ s1 →
    ∃ K1i K2i N P : ℝ, 0 < K1i ∧ 0 < N ∧ 1 ≤ P ∧
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ (F : R3 × R3 → ℝ) (L lam : ℝ) (Ω : Set (R3 × R3)), IsOpen Ω →
      ProductSolutionOn S L lam F Ω → initialCross S lam ⊆ Ω →
      EqOn F (initialKernel S lam) (initialCross S lam) → 0 < lam → lam ≤ lam0 →
      ∀ p : R3, ‖p‖ ≤ B → S.separating_function (lam • p) = 0 → ∀ s ∈ Icc s0 s1,
      ∃ (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3)
        (hTD1 : T ⊆ D1) (ι : Type)
        (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
        D1 = ball (p-(s/20) • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (3*(s/20)) ∧
        T = ball (p-(s/20) • EuclideanSpace.single (2:Fin 3) (1:ℝ)) ((1-α/2)*(s/20)) ∧
        O1 = ball p (α / 4 * (s / 20)) ∧
        CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1
          {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
          (Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8))
          K1i K2i γ1 γ2 ι w μ ∧
        CurrentCrossTensorOn F S lam D1 hD1 O1 hO1D1 T hTD1
          {y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5} K1i K2i γ1 γ2 N w μ ∧
        (∑' i, μ i^(γ1+γ2-1)) ≤ P ∧
        ∃ g : ι → Lp ℝ 2 ((volume:Measure R3).restrict {y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5}),
          (∀ i, currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i
            =ᵐ[(volume:Measure R3).restrict {y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5}] (g i : R3→ℝ)) ∧
          ‖∑' i, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i)‖ ≤ K1i * |K2i| * N * P := by
  obtain ⟨α, Λ, γ2, hα, hα4, hΛ, hγ2, hγ21, hsum1, H1, H2⟩ := range_free_coarse_opening S
  refine ⟨α, hα, hα4, nearGamma Λ α, γ2, by linarith, fun B s0 s1 hB hs0 hss => ?_⟩
  have hs1 : 0 < s1 := hs0.trans_le hss
  obtain ⟨K2i, lamB, -, hlamB, HB⟩ := H2 B s0 s1 hs0 hss
  obtain ⟨K1i, lamA, hK1i, hlamA, HA'⟩ := H1 (B + s1 / 20) (s0 / 20) (s1 / 20)
    (by positivity) (by linarith)
  have he : 0 < α * s0 / 80 := by positivity
  obtain ⟨l1, hl1, Hsep⟩ :=
    exists_uniform_scaled_separating_error S (B + 2 * s1 + 1) (α * s0 / 80) (by positivity) he
  obtain ⟨l2, hl2, Hcross⟩ :=
    exists_uniform_original_lower_cross S (B + 2 * s1 + 1) (α * s0 / 80) (by positivity) he
  have hγ : 0 < nearGamma Λ α+γ2-1 := by linarith
  obtain ⟨lN,N,hlN,hN,HN⟩ := exists_uniform_coarse_actual_product_norms S B s0 s1 α hB hs0 hss hα hα4
  obtain ⟨lP,hlP,hlP1,P,hP,HP⟩ := exists_uniform_coarse_harmonicRestrict_spectrum_power_bound
    S B s0 s1 α (nearGamma Λ α+γ2-1) hB hs0 hss hα hα4 hγ
  refine ⟨K1i,K2i,N,P,hK1i,hN,hP,
    min (min (min l1 l2) (min lamA lamB)) (min lN lP),
    lt_min (lt_min (lt_min hl1 hl2) (lt_min hlamA hlamB)) (lt_min hlN hlP), ?_⟩
  intro F L lam Ω hΩ hSol hΩc hEq hlam hlam0' p hp hp0 s hs
  have hlam0 : lam ≤ min (min l1 l2) (min lamA lamB) := hlam0'.trans (min_le_left _ _)
  have hlN' : lam ≤ lN := hlam0'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlP' : lam ≤ lP := hlam0'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hspos : 0 < s := hs0.trans_le hs.1
  have hl1' : lam ≤ l1 := hlam0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hl2' : lam ≤ l2 := hlam0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hlA : lam ∈ Icc (0 : ℝ) lamA :=
    ⟨hlam.le, hlam0.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hlB : lam ∈ Icc (0 : ℝ) lamB :=
    ⟨hlam.le, hlam0.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
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
  have HA1 := HA' lam hlA c hcB η hηI p hpc
  have HB1 := HB L lam hlB p hp s hs
  have hc2 : c 2 = p 2 - η := by simp [hc_def, PiLp.sub_apply, PiLp.smul_apply]
  have hαη : α * η = α * s / 20 := by rw [hη_def]; ring
  have hαη0 : 0 ≤ α * η := by positivity
  have hαs : α * s0 ≤ α * s := mul_le_mul_of_nonneg_left hs.1 hα.le
  have hαs0 : α * s0 ≤ 1 / 4 * s0 := mul_le_mul_of_nonneg_right hα4 hs0.le
  have hrow : closedBall c ((1 - α / 2) * η) ×ˢ {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s} ⊆ Ω := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply hΩc
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
      closedBall (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8) ⊆ Ω := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply hΩc
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
  obtain ⟨hDo, -, -, -, -, hOK, hKD, -⟩ := native_annulus_target_geometry p s hspos
  have hαη4 := mul_le_mul_of_nonneg_right hα4 hη.le
  have hO1D1 : ball p (α / 4 * η) ⊆ ball c (3 * η) :=
    ball_subset_ball' (by rw [dist_eq_norm, hpc]; linarith)
  have hKTD1 : closedBall c ((1 - α / 2) * η) ⊆ ball c (3 * η) :=
    closedBall_subset_ball (by linarith)
  have hTD1 : ball c ((1 - α / 2) * η) ⊆ ball c (3 * η) := ball_subset_closedBall.trans hKTD1
  obtain ⟨ι, w, μ, hser⟩ := current_cross_series_of_rooms_sum F S L lam Ω hΩ hSol
    (ball c (3 * η)) (ball p (α / 4 * η)) (ball c ((1 - α / 2) * η)) (closedBall c (3 * η))
    (closedBall c ((1 - α / 2) * η))
    {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
    (ball (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8))
    {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s}
    (closedBall (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8))
    isOpen_ball (isConnected_ball (by positivity)) hO1D1 isOpen_ball
    (nonempty_ball.mpr (mul_pos (by linarith) hη)) (isCompact_closedBall _ _)
    ball_subset_closedBall hKTD1
    hTD1 (isCompact_closedBall _ _) ball_subset_closedBall hDo (hOK.trans hKD) isOpen_ball
    (isCompact_native_closed_annulus p (s/2) (2*s)) (fun y hy => ⟨hy.1.le, hy.2.le⟩)
    (isCompact_closedBall _ _) ball_subset_closedBall hrow hobs hK1i (by linarith) HA1 HB1
  obtain ⟨⟨hFrow,hRowN⟩,⟨hFobs,hObsN⟩⟩ := HN F L lam Ω hSol hΩc hEq ⟨hlam,hlN'⟩ p hp hp0 s hs
  have hsys := hser.1
  have harms := currentCoefficient_arms_of_productL2_bounds S L lam Ω hΩ F hSol
    (ball c (3*η)) (closedBall c (3*η)) (ball c ((1-α/2)*η)) (closedBall c ((1-α/2)*η))
    {y:R3 | s/2<‖y-p‖ ∧ ‖y-p‖<2*s} {y:R3 | s/2≤‖y-p‖ ∧ ‖y-p‖≤2*s}
    (ball (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8))
    (closedBall (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8))
    isOpen_ball (isCompact_closedBall _ _) ball_subset_closedBall
    isOpen_ball (isCompact_closedBall _ _) ball_subset_closedBall hTD1
    hDo (isCompact_native_closed_annulus p (s/2) (2*s)) (fun _ hy => ⟨hy.1.le,hy.2.le⟩)
    isOpen_ball (isCompact_closedBall _ _) ball_subset_closedBall hrow hobs
    hFrow hFobs N hN.le hRowN hObsN ι w μ hsys
  have hTensor := currentCrossTensorOn_of_arms_sum F S L lam
    (ball c (3*η)) isOpen_ball (ball p (α/4*η)) hO1D1 (ball c ((1-α/2)*η)) hTD1
    {y:R3 | s/2<‖y-p‖ ∧ ‖y-p‖<2*s} {y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5}
    (ball (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8)) (hOK.trans hKD)
    hK1i hN.le hγ HA1 HB1 w μ hsys hser.2.2.1 harms
  have hPower := HP lam ⟨hlam.le,hlP'⟩ p hp s hs hTD1 ι w w.orthonormal μ hsys.1 hser.2.1 hsys.2.2
  obtain ⟨g,hgae,hBound⟩ := currentCrossTensorOn_exists_norm_bound F S lam
    (ball c (3*η)) isOpen_ball (ball p (α/4*η)) hO1D1 (ball c ((1-α/2)*η)) hTD1
    {y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5}
    K1i K2i (nearGamma Λ α) γ2 N P hK1i.le hN.le w μ hsys.1 hTensor
    (hser.2.2.1 _ hγ) hPower
  have hserN : CurrentCrossSeriesOn F S L lam
    (ball c (3*η)) isOpen_ball (ball p (α/4*η)) hO1D1 (ball c ((1-α/2)*η)) hTD1
    {y:R3 | s/2<‖y-p‖ ∧ ‖y-p‖<2*s} {y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5}
    (ball (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8)) K1i K2i (nearGamma Λ α) γ2 ι w μ :=
    ⟨hsys,hser.2.1,hser.2.2.1,N,hN.le,harms,hTensor⟩
  exact ⟨_,isOpen_ball,_,hO1D1,_,hTD1,ι,w,μ,rfl,rfl,rfl,hserN,hTensor,hPower,g,hgae,hBound⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
