import Calderon.ActualUniformCoarseCrossAmplitude
import Calderon.ActualUniformCurrentCrossKernelJets
import Calderon.ActualCurrentCrossKernelL2Norm
import Calderon.MixedKernelConstruction.MixedKernelClosedCoarseSeed
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open OAI.AnisotropicCalderon.MixedKernelConstructionTask.Geometry
attribute [local instance] Classical.propDecidable

theorem uniform_coarse_full_cross_kernel_with_uniform_jets (S : KnownSideSourceData) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1/4 ∧
      ∀ B s0 s1 : ℝ, 0 < B → 0 < s0 → s0 ≤ s1 →
      ∃ lambda0 C0 : ℝ, ∃ C : ℕ → ℝ, 0 < lambda0 ∧ 0 < C0 ∧ (∀ n, 0 < C n) ∧
      ∀ L lambda : ℝ, lambda ∈ Ioc (0:ℝ) lambda0 →
      ∀ p : R3, ‖p‖ ≤ B → S.separating_function (lambda • p) = 0 → ∀ s ∈ Icc s0 s1,
      let r := α/4*(s/20)
      ∃ K : R3 × R3 → ℝ,
        overlapLarge p r s ⊆ dilatedOffDiagonal S lambda ∧
        ProductSolutionOn S L lambda K (overlapLarge p r s) ∧
        (∀ v ∈ overlapLarge p r s, lambda • v.2 ∈ S.W → K v = dilatedKernel1 S lambda v) ∧
        (∀ v ∈ overlapLarge p r s, lambda • v.1 ∈ S.W → K v = dilatedKernel2 S lambda v) ∧
        (∃ hK : MemLp K 2 (((volume:Measure R3).restrict (ball p r)).prod
          ((volume:Measure R3).restrict {y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5})), ‖hK.toLp K‖ ≤ C0) ∧
        ∀ n : ℕ, ∀ v ∈ overlapRetained p (α*s/1600) s,
          ‖iteratedFDeriv ℝ n K v‖ ≤ C n := by
  obtain ⟨α,hα,hα4,γ1,γ2,hγ,H⟩ := uniform_coarse_cross_series_with_uniform_amplitude S
  refine ⟨α,hα,hα4,?_⟩
  intro B s0 s1 hB hs0 hss
  have hs1 : 0 < s1 := hs0.trans_le hss
  obtain ⟨K1i,K2i,N,P,hK1i,hN,hP,lA,hlA,HA⟩ := H B s0 s1 hB hs0 hss
  obtain ⟨lC,hlC,HC⟩ := exists_uniform_coarse_closed_products_known_cross S B s0 s1 α hB hs0 hss hα hα4
  obtain ⟨lS,hlS,HS⟩ := exists_uniform_scaled_separating_error S (B+2*s1+1) 1 (by positivity) zero_lt_one
  obtain ⟨a,ha,Hmeet⟩ := known_side_meets_open_at_separator S
  obtain ⟨lM,hlM,HM⟩ := exists_uniform_scaled_ball ha hB
  obtain ⟨lJ,hlJ,hlJ1,HJet⟩ := exists_uniform_currentCrossKernel_buffered_jet_bound S (B+2*s1+1) (by positivity)
  let d : ℝ := α*s0/6400
  have hd : 0 < d := by dsimp only [d];positivity
  choose J hJ HJ using fun n => HJet n d hd
  let C0 : ℝ := K1i * |K2i| * N * P+1
  let C (n : ℕ) : ℝ := J n*K1i*|K2i| * N*P+1
  have hC0 : 0 < C0 := by dsimp only [C0]; positivity
  have hC : ∀ n, 0 < C n := by intro n;dsimp only [C];have := hJ n;positivity
  refine ⟨min (min (min lA lC) (min lS lM)) lJ,C0,C,
    lt_min (lt_min (lt_min hlA hlC) (lt_min hlS hlM)) hlJ,hC0,hC,?_⟩
  intro L lambda hlambda p hp hp0 s hs
  have hlam := hlambda.1
  have hOld : lambda ≤ min (min lA lC) (min lS lM) := hlambda.2.trans (min_le_left _ _)
  have hlJ' : lambda ≤ lJ := hlambda.2.trans (min_le_right _ _)
  have hlA' : lambda ≤ lA := hOld.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hlC' : lambda ≤ lC := hOld.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hlS' : lambda ≤ lS := hOld.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlM' : lambda ≤ lM := hOld.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hΩ,hSol,-⟩ := v021_initial_cross_product S L lambda hlam
  obtain ⟨D1,hD1,O1,hO1D1,T,hTD1,ι,w,μ,hD1Eq,hTEq,hO1Eq,hser,hTensor,hPower,g,hgae,hBound⟩ :=
    HA (initialKernel S lambda) L lambda (initialCross S lambda) hΩ hSol subset_rfl (fun _ _ => rfl) hlam hlA' p hp hp0 s hs
  subst D1
  subst T
  subst O1
  let η := s/20
  let c := p-η • EuclideanSpace.single (2:Fin 3) (1:ℝ)
  have hspos : 0 < s := hs0.trans_le hs.1
  have hη : 0 < η := by dsimp only [η];positivity
  have hαη4 := mul_le_mul_of_nonneg_right hα4 hη.le
  have hpη : 0 < α/4*η := by positivity
  obtain ⟨hRow,hObs⟩ := HC lambda ⟨hlam,hlC'⟩ p hp hp0 s hs
  have hobs' : closedBall c (3*η) ×ˢ ball (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8)
      ⊆ initialCross S lambda := (Set.prod_mono subset_rfl ball_subset_closedBall).trans hObs
  obtain ⟨hD2,hO2,hO2o,hO2c,hObsO2,hOK,hKD,hcirc⟩ := native_annulus_target_geometry p s hspos
  have hbox : ball p (α/4*η) ×ˢ {y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5} ⊆ dilatedOffDiagonal S lambda := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    have hy' : 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5 := hy
    have hxp : ‖x-p‖ < α/4*η := by simpa only [mem_ball,dist_eq_norm] using hx
    have hxn : ‖x‖ ≤ B+2*s1+1 := by
      have hn := norm_sub_norm_le x p
      dsimp only [η] at *
      linarith [hs.2]
    have hyn : ‖y‖ ≤ B+2*s1+1 := by
      have hn := norm_sub_norm_le y p
      linarith [hs.2,hy'.2]
    refine ⟨(HS lambda hlam hlS' x hxn).1,(HS lambda hlam hlS' y hyn).1,?_⟩
    intro hxy
    have hxy' : x = y := hxy
    rw [hxy'] at hxp
    dsimp only [η] at *
    linarith [hy'.1]
  have hcp : ‖(p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ))-p‖ = s := by
    rw [sub_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hspos]
    simp
  have hO2S2 : ({y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5} ∩
      ball (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8)).Nonempty :=
    ⟨p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ),hcirc _ hcp,mem_ball_self (by positivity)⟩
  have hpa : lambda • p ∈ ball (0:R3) a := HM lambda hlam hlM' p hp
  obtain ⟨hG,hFirst,h2,h1⟩ := currentCrossKernel_full_crosses S L lambda hlam
    (ball c (3*η)) hD1 (closedBall c (3*η)) (isCompact_closedBall _ _) ball_subset_closedBall
    (ball p (α/4*η)) isOpen_ball hO1D1 (ball c ((1-α/2)*η)) hTD1
    {y:R3 | s/2<‖y-p‖ ∧ ‖y-p‖<2*s} {y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5}
    (ball (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8))
    hO2o hO2c (hOK.trans hKD) isOpen_ball hO2S2 hobs' hbox p (mem_ball_self hpη)
    (fun U hU hpU => Hmeet lambda hlam p hpa hp0 U hU hpU) w μ hser
  obtain ⟨hK,hNorm⟩ := currentCrossKernel_memLp_with_tensor_norm_bound (initialKernel S lambda) S L lambda
    (ball c (3*η)) hD1 (ball p (α/4*η)) isOpen_ball hO1D1 (ball c ((1-α/2)*η)) hTD1
    {y:R3 | s/2<‖y-p‖ ∧ ‖y-p‖<2*s} {y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5}
    (ball (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8)) hO2o (hOK.trans hKD)
    K1i K2i γ1 γ2 ι w μ hser g hgae (K1i * |K2i| * N * P) hBound
  refine ⟨_,hbox,hG,?_,?_,⟨hK,hNorm.trans (by dsimp only [C0];linarith)⟩,?_⟩
  · intro v hv hyW
    exact h1 v.1 ((convex_ball p _).isPreconnected.subset_connectedComponentIn
      (mem_ball_self hpη) subset_rfl hv.1) v.2 hv.2 hyW
  · intro v hv hxW
    exact h2 v.1 hv.1 hxW v.2 hv.2
  · intro n v hv
    have hαs : α*s0 ≤ α*s := mul_le_mul_of_nonneg_left hs.1 hα.le
    have hαspos : 0 < α*s := mul_pos hα hspos
    have hαsMax : α*s ≤ (1/4)*s := mul_le_mul_of_nonneg_right hα4 hspos.le
    have hdSmall : d ≤ s/20 := by dsimp only [d];nlinarith
    have hO1B : ball p (α/4*η) ⊆ ball (0:R3) (B+2*s1+1) := by
      intro x hx
      have hxp : ‖x-p‖ < α/4*η := by simpa only [mem_ball,dist_eq_norm] using hx
      have hn := norm_sub_norm_le x p
      apply mem_ball_zero_iff.mpr
      dsimp only [η] at *
      linarith [hs.2]
    have hO2B : {y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5} ⊆ ball (0:R3) (B+2*s1+1) := by
      intro y hy
      have hn := norm_sub_norm_le y p
      exact mem_ball_zero_iff.mpr (by linarith [hy.2,hs.2])
    have hRet : v.1 ∈ ball p (α*s/1600) ∧ 19*s/20<‖v.2-p‖ ∧ ‖v.2-p‖<21*s/20 := hv
    have hBuffer1 : closedBall v.1 d ⊆ ball p (α/4*η) := by
      intro x hx
      have ht := dist_triangle x v.1 p
      have hxv : dist x v.1 ≤ d := mem_closedBall.mp hx
      have hvp : dist v.1 p < α*s/1600 := mem_ball.mp hRet.1
      apply mem_ball.mpr
      dsimp only [d,η] at *
      nlinarith only [ht,hxv,hvp,hαs,hαspos]
    have hBuffer2 : closedBall v.2 d ⊆ {y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5} := by
      intro y hy
      have hdist : dist y v.2 ≤ d := mem_closedBall.mp hy
      have hUpper := dist_triangle y v.2 p
      have hLower := dist_triangle v.2 y p
      rw [dist_eq_norm v.2 p,dist_eq_norm y p] at hUpper hLower
      rw [dist_comm v.2 y] at hLower
      constructor <;> linarith [hRet.2.1,hRet.2.2]
    have hBoundJet := HJ n lambda ⟨hlam.le,hlJ'⟩ (initialKernel S lambda) L
      (ball c (3*η)) hD1 (ball p (α/4*η)) isOpen_ball hO1D1 (ball c ((1-α/2)*η)) hTD1
      {y:R3 | s/2<‖y-p‖ ∧ ‖y-p‖<2*s} {y:R3 | 4*s/5<‖y-p‖ ∧ ‖y-p‖<6*s/5}
      (ball (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8)) hO2o (hOK.trans hKD)
      hO1B hO2B K1i K2i γ1 γ2 N P hK1i.le hN.le ι w μ hser hTensor hPower v hBuffer1 hBuffer2
    exact hBoundJet.trans (by dsimp only [C];linarith)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
