import Calderon.ActualUniformCoarsePatchTransfer
import Calderon.ActualInitialKernelUniformBound
import Calderon.MixedKernelConstruction.MixedKernelClosedCoarseSeed
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

theorem uniform_coarse_cone_supremum_budget_of_existing_full_cross_solution (S:KnownSideSourceData) :
    ∃ c0:ℝ,0 < c0 ∧ ∀ B d:ℝ,0 < B → 0 < d →
      ∃ Bbig dbig lambda0 N:ℝ,0 < Bbig ∧ 0 < dbig ∧ 0 < lambda0 ∧ 0 < N ∧
      ∀ L lambda:ℝ,lambda∈Ioc (0:ℝ) lambda0 → ∀ (Omega:Set (R3×R3)) (F:R3×R3→ℝ),
      Omega⊆dilatedOffDiagonal S lambda → ProductSolutionOn S L lambda F Omega →
      (∀ z∈Omega,lambda • z.2∈S.W → F z=dilatedKernel1 S lambda z) →
      (∀ z∈Omega,lambda • z.1∈S.W → F z=dilatedKernel2 S lambda z) →
      fixedSeparationSet Bbig dbig⊆Omega → ∀ x y:R3,‖x‖ ≤ B → ‖y‖ ≤ B → d ≤ ‖x-y‖ →
      min (x 2) (y 2) < c0*‖x-y‖ → ‖F (x,y)‖ ≤ N := by
  obtain ⟨alpha1,halpha1,halpha14,H1⟩ := uniform_coarse_patch_jets_of_full_lower_cross_solution S
  obtain ⟨alpha2,halpha2,halpha24,H2⟩ := uniform_coarse_patch_jets_of_full_lower_cross_solution (swappedKnownSideSourceData S)
  let alpha:ℝ := min alpha1 alpha2
  have halpha:0 < alpha := lt_min halpha1 halpha2
  have halpha4:alpha ≤ 1/4 := (min_le_left _ _).trans halpha14
  refine ⟨alpha/8000,by positivity,?_⟩
  intro B d hB hd
  let eta:ℝ := alpha/8000*d
  have heta:0 < eta := by dsimp only [eta];positivity
  obtain ⟨l1,C1,hl1,hC1,HT1⟩ := H1 (2*B) (d/2) (4*B+d) (by positivity) (half_pos hd) (by linarith)
  obtain ⟨l2,C2,hl2,hC2,HT2⟩ := H2 (2*B) (d/2) (4*B+d) (by positivity) (half_pos hd) (by linarith)
  obtain ⟨lC,hlC,HC⟩ := exists_uniform_original_lower_cross S B eta hB heta
  obtain ⟨lA,hlA,HA⟩ := exists_uniform_actual_separating_surface_anchors S (2*B) eta 1 (by positivity) heta (by norm_num)
  obtain ⟨lK,M,hlK,hlK1,hM,HK⟩ := exists_uniform_initialKernel_fixed_separation_bound S B d hB hd
  let Bbig:ℝ := 10*(B+d+1)
  let dbig:ℝ := d/4
  let lambda0:ℝ := min (min l1 l2) (min lC (min lA lK))
  let N:ℝ := max M (max (C1 0) (C2 0))
  refine ⟨Bbig,dbig,lambda0,N,by dsimp only [Bbig];positivity,by dsimp only [dbig];positivity,
    lt_min (lt_min hl1 hl2) (lt_min hlC (lt_min hlA hlK)),hM.trans_le (le_max_left _ _),?_⟩
  intro L lambda hlam Omega F hRoom hF hF1 hF2 hCoverBig
  have hl1':lambda∈Ioc (0:ℝ) l1 := ⟨hlam.1,hlam.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hl2':lambda∈Ioc (0:ℝ) l2 := ⟨hlam.1,hlam.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hlC':lambda ≤ lC := hlam.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlA':lambda ≤ lA := hlam.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hlK':lambda ≤ lK := hlam.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hAnc:∀ p:R3,‖p‖ ≤ 2*B → p 2=0 → ∃ t∈Ioo (-(alpha/8000*d)) (alpha/8000*d),
      S.separating_function (lambda • (p+t • EuclideanSpace.single (2:Fin 3) (1:ℝ)))=0 := by
    intro p hp hp2
    obtain ⟨t,ht,_,_,hZero⟩ := HA lambda hlam.1 hlA' p hp hp2
    exact ⟨t,ht,hZero⟩
  have hPatchFixed (p:R3) (hp:‖p‖ ≤ 2*B) (s:ℝ) (hs:s∈Icc (d/2) (4*B+d)) :
      overlapRetained p (alpha*s/1600) s⊆fixedSeparationSet Bbig dbig := by
    intro z hz
    have hspos:0 < s := (half_pos hd).trans_le hs.1
    have halphas:alpha*s ≤ (1/4)*s := mul_le_mul_of_nonneg_right halpha4 hspos.le
    have hx:‖z.1-p‖ < alpha*s/1600 := by simpa only [mem_ball,dist_eq_norm] using hz.1
    have hy:19*s/20 < ‖z.2-p‖ ∧ ‖z.2-p‖ < 21*s/20 := hz.2
    have hxN:=norm_sub_norm_le z.1 p
    have hyN:=norm_sub_norm_le z.2 p
    have hSep:‖z.2-p‖ ≤ ‖z.1-z.2‖+‖z.1-p‖ := by
      have hh:=dist_triangle z.2 z.1 p
      simpa only [dist_eq_norm,norm_sub_rev] using hh
    change ‖z.1‖ ≤ Bbig ∧ ‖z.2‖ ≤ Bbig ∧ dbig ≤ ‖z.1-z.2‖
    dsimp only [Bbig,dbig]
    constructor
    · linarith only [hxN,hx,halphas,hp,hs.2,hB,hd]
    constructor
    · linarith only [hyN,hy.2,hp,hs.2,hB,hd]
    · linarith only [hSep,hx,hy.1,halphas,hs.1,hd]
  have hSwapF:ProductSolutionOn (swappedKnownSideSourceData S) L lambda
      (fun z:R3×R3 => F (z.2,z.1)) (Prod.swap ⁻¹' Omega) := by
    apply productSolutionOn_of_swapped_source (swappedKnownSideSourceData S) L lambda
    simpa only [swappedKnownSideSourceData_involutive] using hF
  have hWswap:(swappedKnownSideSourceData S).W=S.W := rfl
  have hSwapCross:=full_lower_crosses_of_swapped_source (swappedKnownSideSourceData S) lambda
    (by simpa only [swappedKnownSideSourceData_involutive] using hRoom)
    (by simpa only [swappedKnownSideSourceData_involutive,hWswap] using hF1)
    (by simpa only [swappedKnownSideSourceData_involutive,hWswap] using hF2)
  obtain ⟨_,hInitial,hlow1,hlow2⟩ := known_side_initial_cross_product S L lambda hlam.1
  intro x y hx hy hxy hMin
  have hxyBig:(x,y)∈fixedSeparationSet Bbig dbig := by
    change ‖x‖ ≤ Bbig ∧ ‖y‖ ≤ Bbig ∧ dbig ≤ ‖x-y‖
    dsimp only [Bbig,dbig]
    constructor
    · linarith only [hx,hB,hd]
    constructor
    · linarith only [hy,hB,hd]
    · linarith only [hxy,hd]
  have hxyOmega:(x,y)∈Omega := hCoverBig hxyBig
  have hInitialBudget (hc:(x,y)∈initialCross S lambda):‖F (x,y)‖ ≤ N := by
    have heq:F (x,y)=initialKernel S lambda (x,y) := by
      rcases hc.2 with hxW | hyW
      · exact (hF2 (x,y) hxyOmega hxW).trans (hlow2 (x,y) hc hxW).symm
      · exact (hF1 (x,y) hxyOmega hyW).trans (hlow1 (x,y) hc hyW).symm
    rw [heq,Real.norm_eq_abs]
    exact (HK lambda ⟨hlam.1,hlK'⟩ (x,y) ⟨hx,hy,hxy⟩).trans (le_max_left _ _)
  have hne:x≠y := by intro heq;rw [heq,sub_self,norm_zero] at hxy;linarith only [hxy,hd]
  by_cases hOrder:x 2 ≤ y 2
  · have hxUp:x 2 < alpha/8000*‖x-y‖ := by simpa only [min_eq_left hOrder] using hMin
    by_cases hxLow:x 2 ≤ -eta
    · exact hInitialBudget (HC lambda hlam.1 hlC' (x,y) hx hy hne (Or.inl hxLow))
    · have hxLo:-(alpha/8000*d) < x 2 := lt_of_not_ge hxLow
      obtain ⟨p,s,hp,hzero,hs,hRet⟩ := coarse_cover_one_side halpha halpha4 hd S.separating_function hAnc hx hy hxy hxLo hxUp
      have hr:0 < alpha*s/1600 := by have hspos:0 < s := (half_pos hd).trans_le hs.1;positivity
      have hcap:alpha*s/1600 ≤ alpha1*s/1600 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) ((half_pos hd).trans_le hs.1).le) (by norm_num)
      have hjet:=HT1 L lambda hl1' p hp hzero s hs _ hr hcap Omega F hF
        ((hPatchFixed p hp s hs).trans hCoverBig) hF2 0 (x,y) hRet
      rw [norm_iteratedFDeriv_zero] at hjet
      exact hjet.trans ((le_max_left (C1 0) (C2 0)).trans (le_max_right _ _))
  · have hyUp:y 2 < alpha/8000*‖y-x‖ := by
      have hh:y 2 < alpha/8000*‖x-y‖ := by simpa only [min_eq_right (le_of_not_ge hOrder)] using hMin
      simpa only [norm_sub_rev] using hh
    by_cases hyLow:y 2 ≤ -eta
    · exact hInitialBudget (HC lambda hlam.1 hlC' (x,y) hx hy hne (Or.inr hyLow))
    · have hyLo:-(alpha/8000*d) < y 2 := lt_of_not_ge hyLow
      have hyx:d ≤ ‖y-x‖ := by simpa only [norm_sub_rev] using hxy
      obtain ⟨p,s,hp,hzero,hs,hRet⟩ := coarse_cover_one_side halpha halpha4 hd S.separating_function hAnc hy hx hyx hyLo hyUp
      have hr:0 < alpha*s/1600 := by have hspos:0 < s := (half_pos hd).trans_le hs.1;positivity
      have hcap:alpha*s/1600 ≤ alpha2*s/1600 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_right _ _) ((half_pos hd).trans_le hs.1).le) (by norm_num)
      have hCoverSwap:overlapRetained p (alpha*s/1600) s⊆Prod.swap ⁻¹' Omega := by
        intro z hz
        have hh:=hPatchFixed p hp s hs hz
        apply hCoverBig
        exact ⟨hh.2.1,hh.1,by change dbig ≤ ‖z.2-z.1‖; simpa only [norm_sub_rev] using hh.2.2⟩
      have hjet:=HT2 L lambda hl2' p hp hzero s hs _ hr hcap (Prod.swap ⁻¹' Omega)
        (fun z:R3×R3 => F (z.2,z.1)) hSwapF hCoverSwap hSwapCross.2 0 (y,x) hRet
      rw [norm_iteratedFDeriv_zero] at hjet
      exact hjet.trans ((le_max_right (C1 0) (C2 0)).trans (le_max_right _ _))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
