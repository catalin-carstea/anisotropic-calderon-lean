import MixedKernelMonotoneCurrentPair
import MixedKernelPositiveChartAgreement
import MixedKernelObservedOutputRooms
import MixedKernelCurrentCommonPair
import MixedKernelProductOpenUCP
import MixedKernelCenteredRooms
import MixedKernelFiniteInterpolation
import MixedKernelKnownSideNearOne
import MixedKernelAnnulusGeometry
import MixedKernelKnownSideCompactBuffer
import MixedKernelActualSeparatorAnchors
import MixedKernelKnownSideNeighborhood
import MixedKernelCompatibleGluing
import MixedKernelFullCrossAssembly
import MixedKernelAnchoredKernelConstruction
import Calderon.CollaboratorUCPCarlemanOct17
import MixedKernelClosedUniformFoundation
set_option autoImplicit false
set_option maxHeartbeats 200000
/-! ## v052: compatible common coarse seed (C1-C3 of REPORT.md) -/
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open scoped Matrix.Norms.Elementwise

/-- C1: the ACTUAL full-cross kernel of the range-free coarse series of the ORIGINAL
`initialKernel` at every actual separator zero, on the explicit opening product
`overlapLarge p (α/4 * (s/20)) s`; `α` before the range, `lam0` before `L, lam, p, s`. -/
theorem uniform_coarse_full_cross_kernel_RF (S : KnownSideSourceData) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧
    ∀ B s0 s1 : ℝ, 0 < B → 0 < s0 → s0 ≤ s1 →
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ p : R3, ‖p‖ ≤ B → S.separating_function (lam • p) = 0 → ∀ s ∈ Icc s0 s1,
      ∃ K : R3 × R3 → ℝ,
        overlapLarge p (α / 4 * (s / 20)) s ⊆ dilatedOffDiagonal S lam ∧
        ProductSolutionOn S L lam K (overlapLarge p (α / 4 * (s / 20)) s) ∧
        (∀ v ∈ overlapLarge p (α / 4 * (s / 20)) s, lam • v.2 ∈ S.W →
          K v = dilatedKernel1 S lam v) ∧
        (∀ v ∈ overlapLarge p (α / 4 * (s / 20)) s, lam • v.1 ∈ S.W →
          K v = dilatedKernel2 S lam v) := by
  obtain ⟨α, Λ, γ2, hα, hα4, hΛ, hγ2, hγ21, hsum1, H1, H2⟩ := range_free_coarse_opening S
  refine ⟨α, hα, hα4, fun B s0 s1 hB hs0 hss => ?_⟩
  have hs1 : 0 < s1 := hs0.trans_le hss
  obtain ⟨K2i, lamB, -, hlamB, HB⟩ := H2 B s0 s1 hs0 hss
  obtain ⟨K1i, lamA, hK1i, hlamA, HA'⟩ := H1 (B + s1 / 20) (s0 / 20) (s1 / 20)
    (by positivity) (by linarith)
  have he : 0 < α * s0 / 80 := by positivity
  obtain ⟨l1, hl1, Hsep⟩ :=
    exists_uniform_scaled_separating_error S (B + 2 * s1 + 1) (α * s0 / 80) (by positivity) he
  obtain ⟨l2, hl2, Hcross⟩ :=
    exists_uniform_original_lower_cross S (B + 2 * s1 + 1) (α * s0 / 80) (by positivity) he
  obtain ⟨a2, ha2, Hmeet⟩ := known_side_meets_open_at_separator S
  obtain ⟨lM, hlM, HM⟩ := exists_uniform_scaled_ball ha2 hB
  refine ⟨min (min (min l1 l2) (min lamA lamB)) lM,
    lt_min (lt_min (lt_min hl1 hl2) (lt_min hlamA hlamB)) hlM, ?_⟩
  intro L lam hlam hlam0' p hp hp0 s hs
  have hlam0 : lam ≤ min (min l1 l2) (min lamA lamB) := hlam0'.trans (min_le_left _ _)
  have hlM' : lam ≤ lM := hlam0'.trans (min_le_right _ _)
  obtain ⟨hΩ, hSol, -⟩ := v021_initial_cross_product S L lam hlam
  have hΩc : initialCross S lam ⊆ initialCross S lam := subset_rfl
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
  have hrow : closedBall c ((1 - α / 2) * η) ×ˢ {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s} ⊆
      initialCross S lam := by
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
      closedBall (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8) ⊆
      initialCross S lam := by
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
  obtain ⟨hDo, -, hO2o, hO2c, -, hOK, hKD, hcirc⟩ := native_annulus_target_geometry p s hspos
  have hαη4 := mul_le_mul_of_nonneg_right hα4 hη.le
  have hO1D1 : ball p (α / 4 * η) ⊆ ball c (3 * η) :=
    ball_subset_ball' (by rw [dist_eq_norm, hpc]; linarith)
  have hKTD1 : closedBall c ((1 - α / 2) * η) ⊆ ball c (3 * η) :=
    closedBall_subset_ball (by linarith)
  have hTD1 : ball c ((1 - α / 2) * η) ⊆ ball c (3 * η) := ball_subset_closedBall.trans hKTD1
  obtain ⟨ι, w, μ, hser⟩ := current_cross_series_of_rooms_sum (initialKernel S lam) S L lam
    (initialCross S lam) hΩ hSol
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
  -- C1 (ii)-(v): first/second full identities of the SAME series.
  have hpη : 0 < α / 4 * η := by positivity
  have hO1conn : ball p (α / 4 * η) ⊆ connectedComponentIn (ball p (α / 4 * η)) p :=
    (convex_ball p _).isPreconnected.subset_connectedComponentIn (mem_ball_self hpη) subset_rfl
  have hobs' : closedBall c (3 * η) ×ˢ
      ball (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8) ⊆ initialCross S lam :=
    (prod_mono subset_rfl ball_subset_closedBall).trans hobs
  have hbox : ball p (α / 4 * η) ×ˢ {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5} ⊆
      dilatedOffDiagonal S lam := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hy' : 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5 := hy
    have hxp : ‖x - p‖ < α / 4 * η := by rw [← dist_eq_norm]; exact mem_ball.mp hx
    have hxn : ‖x‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le x p
      linarith [hs.2]
    have hyn : ‖y‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le y p
      linarith [hs.2]
    refine ⟨(Hsep lam hlam hl1' x hxn).1, (Hsep lam hlam hl1' y hyn).1, ?_⟩
    intro hxy
    have hxy' : x = y := hxy
    rw [hxy'] at hxp
    linarith [hy'.1]
  have hcp : ‖(p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) - p‖ = s := by
    rw [sub_sub_cancel_left, norm_neg, norm_smul, he2n, mul_one, Real.norm_eq_abs,
      abs_of_pos hspos]
  have hO2S2 : ({y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5} ∩
      ball (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8)).Nonempty :=
    ⟨p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ), hcirc _ hcp,
      mem_ball_self (by positivity)⟩
  have hpa : lam • p ∈ ball (0 : R3) a2 := HM lam hlam hlM' p hp
  obtain ⟨hG, -, h2, h1⟩ := currentCrossKernel_full_crosses S L lam hlam (ball c (3 * η))
    isOpen_ball (closedBall c (3 * η)) (isCompact_closedBall _ _) ball_subset_closedBall
    (ball p (α / 4 * η)) isOpen_ball hO1D1 (ball c ((1 - α / 2) * η)) hTD1
    {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
    (ball (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8)) hO2o hO2c
    (hOK.trans hKD) isOpen_ball hO2S2 hobs' hbox p (mem_ball_self hpη)
    (fun U hU hpU => Hmeet lam hlam p hpa hp0 U hU hpU) w μ hser
  refine ⟨_, hbox, hG, ?_, ?_⟩
  · intro v hv hyW
    have hv' : v.1 ∈ ball p (α / 4 * η) ∧
        v.2 ∈ {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5} := hv
    exact h1 v.1 (hO1conn hv'.1) v.2 hv'.2 hyW
  · intro v hv hxW
    have hv' : v.1 ∈ ball p (α / 4 * η) ∧
        v.2 ∈ {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5} := hv
    exact h2 v.1 hv'.1 hxW v.2 hv'.2

/-- C2: the two-orientation common seed glued from the C1 kernels of `S` and of the swapped
source at EVERY actual bounded separator zero; retained radius `α s/1600` with `α` before the
range. Compatibility from the checked uniform contact theorems; no contact is assumed. -/
theorem uniform_coarse_two_orientation_seed_RF (S : KnownSideSourceData) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧
    ∀ B s0 s1 : ℝ, 0 < B → 0 < s0 → s0 ≤ s1 →
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∃ (U : Set (R3 × R3)) (H : R3 × R3 → ℝ), IsOpen U ∧ initialCross S lam ⊆ U ∧
        U ⊆ dilatedOffDiagonal S lam ∧ ProductSolutionOn S L lam H U ∧
        EqOn H (initialKernel S lam) (initialCross S lam) ∧
        (∀ v ∈ U, lam • v.2 ∈ S.W → H v = dilatedKernel1 S lam v) ∧
        (∀ v ∈ U, lam • v.1 ∈ S.W → H v = dilatedKernel2 S lam v) ∧
        ∀ p : R3, ‖p‖ ≤ B → S.separating_function (lam • p) = 0 → ∀ s ∈ Icc s0 s1,
          overlapRetained p (α * s / 1600) s ⊆ U ∧
          Prod.swap ⁻¹' overlapRetained p (α * s / 1600) s ⊆ U := by
  obtain ⟨α1, hα1, hα14, H1⟩ := uniform_coarse_full_cross_kernel_RF S
  obtain ⟨α2, hα2, hα24, H2⟩ :=
    uniform_coarse_full_cross_kernel_RF (swappedKnownSideSourceData S)
  obtain ⟨α, hα, hα4, hαa, hαb⟩ : ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ α ≤ α1 ∧ α ≤ α2 :=
    ⟨min α1 α2, lt_min hα1 hα2, (min_le_left _ _).trans hα14, min_le_left _ _,
      min_le_right _ _⟩
  refine ⟨α, hα, hα4, fun B s0 s1 hB hs0 hss => ?_⟩
  have hs1 : 0 < s1 := hs0.trans_le hss
  obtain ⟨lamI, hlI, HI⟩ := H1 B s0 s1 hB hs0 hss
  obtain ⟨lamJ, hlJ, HJ⟩ := H2 B s0 s1 hB hs0 hss
  obtain ⟨lamA, hlA, HA⟩ := uniform_retained_same_orientation_contact S B s1 hB hs1
  obtain ⟨lamB, hlB, HB⟩ :=
    uniform_retained_same_orientation_contact (swappedKnownSideSourceData S) B s1 hB hs1
  obtain ⟨lamC, hlC, HC⟩ := uniform_retained_opposite_orientation_contact S B s1 hB hs1
  refine ⟨min (min lamI lamJ) (min lamA (min lamB lamC)),
    lt_min (lt_min hlI hlJ) (lt_min hlA (lt_min hlB hlC)), fun L lam hlam hle => ?_⟩
  have hI : lam ≤ lamI := hle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hJ : lam ≤ lamJ := hle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hA : lam ≤ lamA := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hB' : lam ≤ lamB :=
    hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hC : lam ≤ lamC :=
    hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hIo, hIsol, hI1, hI2⟩ := v021_initial_cross_product S L lam hlam
  let A : Type :=
    {ps : R3 × ℝ // ‖ps.1‖ ≤ B ∧ S.separating_function (lam • ps.1) = 0 ∧ ps.2 ∈ Icc s0 s1}
  have hex := fun i : A => HI L lam hlam hI i.1.1 i.2.1 i.2.2.1 i.1.2 i.2.2.2
  choose K hroom hK hK1 hK2 using hex
  have hex' := fun j : A => HJ L lam hlam hJ j.1.1 j.2.1 j.2.2.1 j.1.2 j.2.2.2
  choose K' hroom' hK' hK1' hK2' using hex'
  let R : A → ℝ := fun i => α1 / 4 * (i.1.2 / 20)
  let R' : A → ℝ := fun j => α2 / 4 * (j.1.2 / 20)
  let r : A → ℝ := fun i => α * i.1.2 / 1600
  have hspos : ∀ i : A, 0 < i.1.2 := fun i => hs0.trans_le i.2.2.2.1
  have hr : ∀ i : A, 0 < r i := fun i => div_pos (mul_pos hα (hspos i)) (by norm_num)
  have h20 : ∀ i : A, 20 * r i ≤ R i := fun i => by
    have := mul_le_mul_of_nonneg_right hαa (hspos i).le
    show 20 * (α * i.1.2 / 1600) ≤ α1 / 4 * (i.1.2 / 20)
    linarith
  have h20' : ∀ j : A, 20 * r j ≤ R' j := fun j => by
    have := mul_le_mul_of_nonneg_right hαb (hspos j).le
    show 20 * (α * j.1.2 / 1600) ≤ α2 / 4 * (j.1.2 / 20)
    linarith
  have hrs : ∀ i : A, r i ≤ i.1.2 / 1000 := fun i => by
    have := mul_le_mul_of_nonneg_right hα4 (hspos i).le
    show α * i.1.2 / 1600 ≤ i.1.2 / 1000
    linarith [hspos i]
  have hrs1 : ∀ i : A, r i ≤ s1 := fun i => (hrs i).trans (by linarith [i.2.2.2.2, hspos i])
  have hsub : ∀ i, overlapRetained i.1.1 (r i) i.1.2 ⊆ overlapLarge i.1.1 (R i) i.1.2 :=
    fun i => overlapRetained_subset_large (by linarith [hr i, h20 i])
  have hsub' : ∀ j, overlapRetained j.1.1 (r j) j.1.2 ⊆ overlapLarge j.1.1 (R' j) j.1.2 :=
    fun j => overlapRetained_subset_large (by linarith [hr j, h20' j])
  have hT := fun j => full_lower_crosses_of_swapped_source S lam (hroom' j) (hK1' j) (hK2' j)
  have hroomT : ∀ j, ∀ v ∈ Prod.swap ⁻¹' overlapLarge j.1.1 (R' j) j.1.2,
      v ∈ dilatedOffDiagonal S lam := fun j v hv => by
    have hh : lam • v.2 ∈ S.coordinateRoom ∧ lam • v.1 ∈ S.coordinateRoom ∧ v.2 ≠ v.1 :=
      hroom' j hv
    exact ⟨hh.2.1, hh.1, fun h => hh.2.2 h.symm⟩
  let Uf : Option (A ⊕ A) → Set (R3 × R3) := fun o => o.elim (initialCross S lam)
    (Sum.elim (fun i => overlapRetained i.1.1 (r i) i.1.2)
      (fun j => Prod.swap ⁻¹' overlapRetained j.1.1 (r j) j.1.2))
  let F : Option (A ⊕ A) → R3 × R3 → ℝ := fun o => o.elim (initialKernel S lam)
    (Sum.elim K (fun j v => K' j (v.2,v.1)))
  have hUo : ∀ o, IsOpen (Uf o) := by
    rintro (_ | i | j)
    · exact hIo
    · exact isOpen_overlapRetained _ _ _
    · exact (isOpen_overlapRetained _ _ _).preimage continuous_swap
  have hF : ∀ o, ProductSolutionOn S L lam (F o) (Uf o) := by
    rintro (_ | i | j)
    · exact hIsol
    · exact productSolutionOn_mono (hK i) (hsub i)
    · exact productSolutionOn_of_swapped_source S L lam
        (productSolutionOn_mono (hK' j) (hsub' j))
  have hIK : ∀ i, EqOn (K i) (initialKernel S lam)
      (overlapRetained i.1.1 (r i) i.1.2 ∩ initialCross S lam) :=
    fun i v hv => retained_eq_initialKernel S lam (hK1 i) (hK2 i) ⟨hsub i hv.1, hv.2⟩
  have hIK' : ∀ j, EqOn (fun v : R3 × R3 => K' j (v.2,v.1)) (initialKernel S lam)
      (Prod.swap ⁻¹' overlapRetained j.1.1 (r j) j.1.2 ∩ initialCross S lam) :=
    fun j v hv => retained_eq_initialKernel S lam (hT j).1 (hT j).2 ⟨hsub' j hv.1, hv.2⟩
  have hSS : ∀ i i', EqOn (K i) (K i')
      (overlapRetained i.1.1 (r i) i.1.2 ∩ overlapRetained i'.1.1 (r i') i'.1.2) :=
    fun i i' => HA L lam hlam hA i.1.1 i'.1.1 (R i) (R i') (r i) (r i') i.1.2 i'.1.2
      i.2.1 i'.2.1 i.2.2.1 i'.2.2.1 (h20 i) (h20 i') (hrs1 i) (hrs1 i') (K i) (K i')
      (hK i) (hK i') (hK2 i) (hK2 i')
  have hTT : ∀ j j', EqOn (K' j) (K' j')
      (overlapRetained j.1.1 (r j) j.1.2 ∩ overlapRetained j'.1.1 (r j') j'.1.2) :=
    fun j j' => HB L lam hlam hB' j.1.1 j'.1.1 (R' j) (R' j') (r j) (r j') j.1.2 j'.1.2
      j.2.1 j'.2.1 j.2.2.1 j'.2.2.1 (h20' j) (h20' j') (hrs1 j) (hrs1 j')
      (K' j) (K' j') (hK' j) (hK' j') (hK2' j) (hK2' j')
  have hST : ∀ i j, ∀ v : R3 × R3, v ∈ overlapRetained i.1.1 (r i) i.1.2 →
      Prod.swap v ∈ overlapRetained j.1.1 (r j) j.1.2 → K i v = K' j (v.2,v.1) :=
    fun i j => HC L lam hlam hC i.1.1 j.1.1 (R i) (R' j) (r i) (r j) i.1.2 j.1.2 i.2.1
      i.2.2.1 (h20 i) (h20' j) (hrs i) (hrs j) (hrs1 i) (K i) (K' j) (hK i) (hK2 i)
      (hK' j) (hroom' j) (hK1' j) (hK2' j)
  have hcomp : ∀ o o', EqOn (F o) (F o') (Uf o ∩ Uf o') := by
    rintro (_ | i | j) (_ | i' | j') v hv
    · rfl
    · exact (hIK i' ⟨hv.2, hv.1⟩).symm
    · exact (hIK' j' ⟨hv.2, hv.1⟩).symm
    · exact hIK i hv
    · exact hSS i i' hv
    · exact hST i j' v hv.1 hv.2
    · exact hIK' j hv
    · exact (hST i' j v hv.2 hv.1).symm
    · exact hTT j j' hv
  obtain ⟨H, hH, hHe⟩ := exists_productSolutionOn_iUnion S L lam Uf hUo F hF hcomp
  have hUeq : (⋃ o, Uf o) = initialCross S lam ∪ ((⋃ i, overlapRetained i.1.1 (r i) i.1.2) ∪
      ⋃ j, Prod.swap ⁻¹' overlapRetained j.1.1 (r j) j.1.2) := by
    ext v
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨_ | i | j, hv⟩
      · exact Or.inl hv
      · exact Or.inr (Or.inl ⟨i, hv⟩)
      · exact Or.inr (Or.inr ⟨j, hv⟩)
    · rintro (hv | ⟨i, hv⟩ | ⟨j, hv⟩)
      · exact ⟨none, hv⟩
      · exact ⟨some (Sum.inl i), hv⟩
      · exact ⟨some (Sum.inr j), hv⟩
  have hHI : EqOn H (initialKernel S lam) (initialCross S lam) := hHe none
  have hHK : ∀ i, EqOn H (K i) (overlapRetained i.1.1 (r i) i.1.2) :=
    fun i => hHe (some (Sum.inl i))
  have hHK' : ∀ j, EqOn H (fun v => K' j (v.2,v.1))
      (Prod.swap ⁻¹' overlapRetained j.1.1 (r j) j.1.2) := fun j => hHe (some (Sum.inr j))
  refine ⟨_, H,
    hIo.union ((isOpen_iUnion fun i => isOpen_overlapRetained _ _ _).union
      (isOpen_iUnion fun j => (isOpen_overlapRetained _ _ _).preimage continuous_swap)),
    subset_union_left, ?_, by rw [← hUeq]; exact hH, hHI, ?_, ?_, ?_⟩
  · rintro v (hv | hv | hv)
    · exact hv.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hv
      exact hroom i (hsub i hi)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hv
      exact hroomT j v (hsub' j hj)
  · rintro v (hv | hv | hv) hW
    · rw [hHI hv]; exact hI1 v hv hW
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hv
      rw [hHK i hi]; exact hK1 i v (hsub i hi) hW
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hv
      rw [hHK' j hj]; exact (hT j).1 v (hsub' j hj) hW
  · rintro v (hv | hv | hv) hW
    · rw [hHI hv]; exact hI2 v hv hW
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hv
      rw [hHK i hi]; exact hK2 i v (hsub i hi) hW
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hv
      rw [hHK' j hj]; exact (hT j).2 v (hsub' j hj) hW
  · intro p hp hp0 s hs
    let i : A := ⟨(p, s), hp, hp0, hs⟩
    exact ⟨fun v hv => Or.inr (Or.inl (mem_iUnion.mpr ⟨i, hv⟩)),
      fun v hv => Or.inr (Or.inr (mem_iUnion.mpr ⟨i, hv⟩))⟩

/-- Lemma G: a pair whose first point is within `α‖x-y‖/4000` of `z` lies in the retained
product of radius `α s/1600` about `z`, `s = ‖y - z‖`. -/
theorem retained_mem_of_near_anchor {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {x y z : R3}
    (hxz : ‖x - z‖ < α * ‖x - y‖ / 4000) :
    ‖x - y‖ / 2 < ‖y - z‖ ∧ ‖y - z‖ ≤ ‖x - y‖ + ‖x - z‖ ∧
      (x, y) ∈ overlapRetained z (α * ‖y - z‖ / 1600) ‖y - z‖ := by
  have hδ0 : 0 ≤ ‖x - z‖ := norm_nonneg _
  have h1 : α * ‖x - y‖ ≤ 1 / 4 * ‖x - y‖ := mul_le_mul_of_nonneg_right hα4 (norm_nonneg _)
  have hlo : ‖x - y‖ ≤ ‖x - z‖ + ‖y - z‖ := by
    have h := norm_sub_le (x - z) (y - z)
    rwa [sub_sub_sub_cancel_right] at h
  have hup : ‖y - z‖ ≤ ‖x - y‖ + ‖x - z‖ := by
    have h := norm_sub_le_norm_sub_add_norm_sub y x z
    rw [norm_sub_rev y x] at h
    exact h
  have hs : ‖x - y‖ / 2 < ‖y - z‖ := by linarith
  have h2 : α * (‖x - y‖ / 2) ≤ α * ‖y - z‖ := mul_le_mul_of_nonneg_left hs.le hα.le
  refine ⟨hs, hup, ?_⟩
  show x ∈ ball z (α * ‖y - z‖ / 1600) ∧
    (19 * ‖y - z‖ / 20 < ‖y - z‖ ∧ ‖y - z‖ < 21 * ‖y - z‖ / 20)
  have hspos : 0 < ‖y - z‖ := by linarith
  refine ⟨?_, by linarith, by linarith⟩
  rw [mem_ball, dist_eq_norm]
  linarith

/-- The vertical anchor below `x`: `x - ((x - x₂ e₂) + t e₂) = (x₂ - t) e₂`. -/
theorem near_plane_anchor_dist {x : R3} {t : ℝ} :
    ‖x - ((x - x 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) +
      t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ = |x 2 - t| := by
  have h : x - ((x - x 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) +
      t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) =
      (x 2 - t) • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    rw [sub_smul]; abel
  rw [h, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]

/-- One-sided coverage on its genuine near-plane branch; points deeper below are in initialCross. -/
theorem coarse_cover_one_side {α B d lam : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hd : 0 < d)
    (sep : R3 → ℝ)
    (hanc : ∀ p : R3, ‖p‖ ≤ 2 * B → p 2 = 0 → ∃ t ∈ Ioo (-(α / 8000 * d)) (α / 8000 * d),
      sep (lam • (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) = 0)
    {x y : R3} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) (hxy : d ≤ ‖x - y‖)
    (hlo : -(α / 8000 * d) < x 2) (hup : x 2 < α / 8000 * ‖x - y‖) :
    ∃ (z : R3) (s : ℝ), ‖z‖ ≤ 2 * B ∧ sep (lam • z) = 0 ∧ s ∈ Icc (d / 2) (4 * B + d) ∧
      (x, y) ∈ overlapRetained z (α * s / 1600) s := by
  have hen : ‖EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ = 1 := by
    rw [EuclideanSpace.norm_single, norm_one]
  have hx2 : |x 2| ≤ ‖x‖ := abs_coord_le_norm x 2
  have hB0 : 0 ≤ B := (norm_nonneg x).trans hx
  have hpn : ‖x - x 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ 2 * B := by
    have h := norm_sub_le x (x 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    rw [norm_smul, hen, mul_one, Real.norm_eq_abs] at h
    linarith
  have hp2 : (x - x 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) 2 = 0 := by
    simp [PiLp.sub_apply, PiLp.smul_apply]
  obtain ⟨t, ht, hsep⟩ := hanc _ hpn hp2
  let z := (x - x 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))+
    t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have hEps : α / 8000 * d ≤ α / 8000 * ‖x-y‖ :=
    mul_le_mul_of_nonneg_left hxy (by positivity)
  have hdist : ‖x-z‖ < α*‖x-y‖/4000 := by
    rw [show ‖x-z‖ = |x 2-t| from near_plane_anchor_dist]
    apply abs_lt.mpr
    constructor <;> linarith [ht.1,ht.2]
  have hgeom := retained_mem_of_near_anchor hα hα4 hdist
  have hD : ‖x-y‖ ≤ 2*B := (norm_sub_le x y).trans (by linarith)
  have hαD : α*‖x-y‖ ≤ (1/4 : ℝ)*‖x-y‖ :=
    mul_le_mul_of_nonneg_right hα4 (norm_nonneg _)
  have hzNear : ‖z‖ ≤ ‖x‖+‖x-z‖ := by
    have hh := norm_add_le x (z-x)
    have hEq : x+(z-x) = z := by abel
    rw [hEq,norm_sub_rev z x] at hh
    exact hh
  have hzB : ‖z‖ ≤ 2*B := by linarith
  have hsUpper : ‖y-z‖ ≤ 4*B+d := by
    have hh := norm_sub_le y z
    linarith
  exact ⟨z,‖y-z‖,hzB,hsep,⟨by linarith [hgeom.1],hsUpper⟩,hgeom.2.2⟩

/-- One common ACTUAL coarse seed, with c0 chosen BEFORE every bounded positive-separation range. -/
theorem uniform_common_coarse_seed_RF (S : KnownSideSourceData) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ B d : ℝ, 0 < B → 0 < d →
      ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
        ∃ (U : Set (R3 × R3)) (H : R3 × R3 → ℝ), IsOpen U ∧ initialCross S lam ⊆ U ∧
          U ⊆ dilatedOffDiagonal S lam ∧ ProductSolutionOn S L lam H U ∧
          EqOn H (initialKernel S lam) (initialCross S lam) ∧
          (∀ v ∈ U, lam • v.2 ∈ S.W → H v = dilatedKernel1 S lam v) ∧
          (∀ v ∈ U, lam • v.1 ∈ S.W → H v = dilatedKernel2 S lam v) ∧
          ∀ x y : R3, ‖x‖ ≤ B → ‖y‖ ≤ B → d ≤ ‖x-y‖ →
            min (x 2) (y 2) < c0*‖x-y‖ → (x,y) ∈ U := by
  obtain ⟨α,hα,hα4,HSeed⟩ := uniform_coarse_two_orientation_seed_RF S
  refine ⟨α/8000,by positivity,?_⟩
  intro B d hB hd
  let eta : ℝ := α/8000*d
  have heta : 0 < eta := by dsimp [eta];positivity
  obtain ⟨lS,hlS,HS⟩ := HSeed (2*B) (d/2) (4*B+d) (by positivity) (half_pos hd) (by linarith)
  obtain ⟨lC,hlC,HC⟩ := exists_uniform_original_lower_cross S B eta hB heta
  obtain ⟨lA,hlA,HA⟩ := exists_uniform_actual_separating_surface_anchors S (2*B) eta 1
    (by positivity) heta (by norm_num)
  refine ⟨min lS (min lC lA),lt_min hlS (lt_min hlC hlA),?_⟩
  intro L lam hlam hlam0
  have hLS : lam ≤ lS := hlam0.trans (min_le_left _ _)
  have hLC : lam ≤ lC := hlam0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hLA : lam ≤ lA := hlam0.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨U,H,hU,hI,hRoom,hSol,hHI,hH1,hH2,hCover⟩ := HS L lam hlam hLS
  have hAnc : ∀ p : R3, ‖p‖ ≤ 2*B → p 2 = 0 →
      ∃ t ∈ Ioo (-(α/8000*d)) (α/8000*d),
        S.separating_function (lam • (p+t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) = 0 := by
    intro p hp hp2
    obtain ⟨t,ht,_,_,hZero⟩ := HA lam hlam hLA p hp hp2
    exact ⟨t,ht,hZero⟩
  refine ⟨U,H,hU,hI,hRoom,hSol,hHI,hH1,hH2,?_⟩
  intro x y hx hy hxy hMin
  have hne : x ≠ y := by
    intro heq
    rw [heq,sub_self,norm_zero] at hxy
    linarith
  by_cases hOrder : x 2 ≤ y 2
  · have hxUp : x 2 < α/8000*‖x-y‖ := by simpa only [min_eq_left hOrder] using hMin
    by_cases hxLow : x 2 ≤ -eta
    · exact hI (HC lam hlam hLC (x,y) hx hy hne (Or.inl hxLow))
    · have hxLo : -(α/8000*d) < x 2 := lt_of_not_ge hxLow
      obtain ⟨z,s,hz,hzero,hs,hRet⟩ := coarse_cover_one_side hα hα4 hd S.separating_function hAnc
        hx hy hxy hxLo hxUp
      exact (hCover z hz hzero s hs).1 hRet
  · have hyUp : y 2 < α/8000*‖y-x‖ := by
      have hh : y 2 < α/8000*‖x-y‖ := by
        simpa only [min_eq_right (le_of_not_ge hOrder)] using hMin
      simpa only [norm_sub_rev] using hh
    by_cases hyLow : y 2 ≤ -eta
    · exact hI (HC lam hlam hLC (x,y) hx hy hne (Or.inr hyLow))
    · have hyLo : -(α/8000*d) < y 2 := lt_of_not_ge hyLow
      have hyx : d ≤ ‖y-x‖ := by simpa only [norm_sub_rev] using hxy
      obtain ⟨z,s,hz,hzero,hs,hRet⟩ := coarse_cover_one_side hα hα4 hd S.separating_function hAnc
        hy hx hyx hyLo hyUp
      exact (hCover z hz hzero s hs).2 hRet

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

