import Calderon.ActualInitialKernelUniformProductNorm
import Calderon.ActualCoarseProductSeparation
import Calderon.ActualCoarseProductsKnownCross
import MixedKernelCurrentCrossBounds
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Geometry
attribute [local instance] Classical.propDecidable

theorem exists_uniform_coarse_actual_product_norms
    (S : KnownSideSourceData) (B s0 s1 α : ℝ)
    (hB : 0 < B) (hs0 : 0 < s0) (hss : s0 ≤ s1) (hα : 0 < α) (hα4 : α ≤ 1/4) :
    ∃ lambda0 N : ℝ, 0 < lambda0 ∧ 0 < N ∧
      ∀ (F : R3 × R3 → ℝ) (L lambda : ℝ) (Ω : Set (R3 × R3)),
      ProductSolutionOn S L lambda F Ω → initialCross S lambda ⊆ Ω →
      EqOn F (initialKernel S lambda) (initialCross S lambda) →
      lambda ∈ Ioc (0:ℝ) lambda0 → ∀ p : R3, ‖p‖ ≤ B →
      S.separating_function (lambda • p) = 0 → ∀ s ∈ Icc s0 s1,
      let η := s/20
      let c := p-η • EuclideanSpace.single (2:Fin 3) (1:ℝ)
      (∃ hF : MemLp F 2 (((volume:Measure R3).restrict (ball c ((1-α/2)*η))).prod
        ((volume:Measure R3).restrict {y:R3 | s/2<‖y-p‖ ∧ ‖y-p‖<2*s})), ‖hF.toLp F‖ ≤ N) ∧
      (∃ hF : MemLp F 2 (((volume:Measure R3).restrict (ball c (3*η))).prod
        ((volume:Measure R3).restrict (ball (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8)))),
        ‖hF.toLp F‖ ≤ N) := by
  have hs1 : 0 < s1 := hs0.trans_le hss
  obtain ⟨ln,N,hln,hln1,hN,hNorm⟩ := exists_uniform_initialKernel_product_L2_bound
    S (B+2*s1+1) (s0/4) (by positivity) (by positivity)
  obtain ⟨lc,hlc,hCross⟩ := exists_uniform_coarse_closed_products_known_cross S B s0 s1 α hB hs0 hss hα hα4
  refine ⟨min ln lc,N,lt_min hln hlc,hN,?_⟩
  intro F L lambda Ω hSol hΩc hEq hlambda p hp hp0 s hs
  let η := s/20
  let c := p-η • EuclideanSpace.single (2:Fin 3) (1:ℝ)
  let D2 : Set R3 := {y:R3 | s/2<‖y-p‖ ∧ ‖y-p‖<2*s}
  let J2 : Set R3 := {y:R3 | s/2≤‖y-p‖ ∧ ‖y-p‖≤2*s}
  let S2 := ball (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8)
  let JS := closedBall (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8)
  have hlnI : lambda ∈ Ioc (0:ℝ) ln := ⟨hlambda.1,hlambda.2.trans (min_le_left _ _)⟩
  have hlcI : lambda ∈ Ioc (0:ℝ) lc := ⟨hlambda.1,hlambda.2.trans (min_le_right _ _)⟩
  obtain ⟨hRowCross,hObsCross⟩ := hCross lambda hlcI p hp hp0 s hs
  obtain ⟨hRowSep,hObsSep⟩ := coarse_closed_products_subset_fixedSeparation B s0 s1 α hB hs0 hss hα hα4 p hp s hs
  have hD2J2 : D2 ⊆ J2 := fun y hy => ⟨hy.1.le,hy.2.le⟩
  have hRowSmall : ball c ((1-α/2)*η) ×ˢ D2 ⊆ closedBall c ((1-α/2)*η) ×ˢ J2 :=
    Set.prod_mono ball_subset_closedBall hD2J2
  have hObsSmall : ball c (3*η) ×ˢ S2 ⊆ closedBall c (3*η) ×ˢ JS :=
    Set.prod_mono ball_subset_closedBall ball_subset_closedBall
  have hspos : 0 < s := hs0.trans_le hs.1
  obtain ⟨hD2Open,-,-,-,-,-,-,-⟩ := native_annulus_target_geometry p s hspos
  have hRowMem := productCurrent_memLp_product Ω F hSol.1
    (ball c ((1-α/2)*η)) D2 (closedBall c ((1-α/2)*η)) J2
    isOpen_ball hD2Open (isCompact_closedBall _ _) (isCompact_native_closed_annulus p (s/2) (2*s))
    ball_subset_closedBall hD2J2 (hRowCross.trans hΩc)
  have hObsMem := productCurrent_memLp_product Ω F hSol.1
    (ball c (3*η)) S2 (closedBall c (3*η)) JS
    isOpen_ball isOpen_ball (isCompact_closedBall _ _) (isCompact_closedBall _ _)
    ball_subset_closedBall ball_subset_closedBall (hObsCross.trans hΩc)
  constructor
  · refine ⟨hRowMem,?_⟩
    exact hNorm lambda hlnI _ _ isOpen_ball.measurableSet hD2Open.measurableSet
      (hRowSmall.trans hRowSep) F (hEq.mono (hRowSmall.trans hRowCross)) hRowMem
  · refine ⟨hObsMem,?_⟩
    exact hNorm lambda hlnI _ _ isOpen_ball.measurableSet isOpen_ball.measurableSet
      (hObsSmall.trans hObsSep) F (hEq.mono (hObsSmall.trans hObsCross)) hObsMem

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
