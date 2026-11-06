import Calderon.ActualEuclideanConvexProductPhase
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

theorem exists_uniform_compact_interior_existing_product_jet_estimate
    (S:KnownSideSourceData) (K U:Set (R3×R3)) (hK:IsCompact K) (hU:IsOpen U) (hKU:K⊆U)
:
    ∃ lambda0:ℝ,0 < lambda0 ∧ ∃ Ksource V:Set (R3×R3),
      IsCompact Ksource ∧ Ksource⊆U ∧
      IsOpen V ∧ K⊆V ∧ V⊆U ∧ ∃ C:ℕ→ℝ,(∀ n,0 < C n) ∧
      ∀ L:ℝ,∀ lambda∈Icc (0:ℝ) lambda0,∀ F:R3×R3→ℝ,ProductSolutionOn S L lambda F U →
      ∀ M:ℝ,0 ≤ M → (∀ z∈Ksource,‖F z‖ ≤ M) →
      ∀ n:ℕ,∀ z∈V,‖iteratedFDeriv ℝ n F z‖ ≤ C n*M := by
  choose ell rad hell hrad KS hKS hKSpos hSmall C hC H using fun p:K =>
    exists_uniform_existing_product_solution_local_jet_estimate S p.val.1 p.val.2 U hU (hKU p.property)
      (convexProductPhase p.val) (convexProductPhase_contDiff_and_zero p.val).1.contDiffOn
      (convexProductPhase_contDiff_and_zero p.val).2
      (by simpa only [zero_smul,S.g1_origin,S.g2_origin] using convexProductPhase_flat_strict p.val)
  have hCover:K⊆⋃p:K,ball p.val (rad p) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (hrad ⟨x,hx⟩)⟩
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun p:K => ball p.val (rad p)) (fun _ => isOpen_ball) hCover
  have hLower:∀ s:Finset K,∃ l:ℝ,0 < l ∧ ∀ p∈s,l ≤ ell p := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert p s hp ih =>
      obtain ⟨l,hl,Hl⟩ := ih
      refine ⟨min l (ell p),lt_min hl (hell p),?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with heq | hq
      · subst q;exact min_le_right _ _
      · exact (min_le_left _ _).trans (Hl q hq)
  obtain ⟨lambda0,hlambda0,hLambda⟩ := hLower t
  have hBounds:∀ n:ℕ,∃ B:ℝ,∀ p∈t,C p n ≤ B := by
    intro n
    obtain ⟨B,hB⟩ := (t.finite_toSet.image (fun p => C p n)).bddAbove
    exact ⟨B,fun p hp => hB (Set.mem_image_of_mem _ hp)⟩
  choose B hB using hBounds
  let Ksource:Set (R3×R3) := ⋃p∈t,KS p
  let V:Set (R3×R3) := ⋃p∈t,ball p.val (rad p)
  have hKsource:IsCompact Ksource := t.isCompact_biUnion (fun p _ => hKS p)
  have hKsourcePos:Ksource⊆U := by
    intro z hz
    obtain ⟨p,hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hp,hz⟩ := Set.mem_iUnion.mp hz
    exact (hKSpos p hz).1
  have hV:IsOpen V := isOpen_iUnion fun p => isOpen_iUnion fun _ => isOpen_ball
  have hVU:V⊆U := by
    intro z hz
    obtain ⟨p,hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hp,hz⟩ := Set.mem_iUnion.mp hz
    exact hSmall p hz
  let C0:ℕ→ℝ := fun n => max (B n) 1
  refine ⟨lambda0,hlambda0,Ksource,V,hKsource,hKsourcePos,hV,ht,hVU,C0,
    (fun n => zero_lt_one.trans_le (le_max_right _ _)),?_⟩
  intro L lambda hlam F hF M hM hBound n z hz
  obtain ⟨p,hz⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hp,hz⟩ := Set.mem_iUnion.mp hz
  have hBudget:∀ x∈KS p,‖F x‖ ≤ M := fun x hx => hBound x
    (Set.mem_iUnion.mpr ⟨p,Set.mem_iUnion.mpr ⟨hp,hx⟩⟩)
  have h:=H p L lambda ⟨hlam.1,hlam.2.trans (hLambda p hp)⟩ F hF M hM hBudget n z hz
  exact h.trans (mul_le_mul_of_nonneg_right ((hB n p hp).trans (le_max_left _ _)) hM)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
