import Calderon.ActualFiniteLevelBudgetPropagation
import Calderon.MixedKernelConstruction.MixedKernelClosedUniformFoundation
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable

theorem exists_compact_band_product_supremum_budget_of_positive_local_estimates
    (S:KnownSideSourceData) (K Seed U:Set (R3×R3)) (hK:IsCompact K) (hSeed:IsOpen Seed)
    (hU:IsOpen U) (hKU:K⊆U) (level:R3×R3→ℝ) (hLevel:ContinuousOn level U)
    (lo hi:ℝ) (hBand:∀ x∈K,lo ≤ level x ∧ level x ≤ hi)
    (hHigh:∀ y∈U,lo ≤ level y → y∈Seed ∨ y∈K)
    (hLocal:∀ p∈K,p∉Seed → ∃ lambda0 r:ℝ,0 < lambda0 ∧ 0 < r ∧
      ∃ KS:Set (R3×R3),IsCompact KS ∧ KS⊆{y | y∈U ∧ level p < level y} ∧
      ball p r⊆U ∧ ∃ C:ℝ,0 < C ∧
      ∀ L:ℝ,∀ lambda∈Icc (0:ℝ) lambda0,∀ F:R3×R3→ℝ,ProductSolutionOn S L lambda F U →
      ∀ T:ℝ,0 ≤ T → (∀ y∈KS,‖F y‖ ≤ T) → ∀ x∈ball p r,‖F x‖ ≤ C*T) :
    ∃ lambda0 C:ℝ,0 < lambda0 ∧ 0 < C ∧
      ∀ L:ℝ,∀ lambda∈Icc (0:ℝ) lambda0,∀ F:R3×R3→ℝ,ProductSolutionOn S L lambda F U →
      ∀ M:ℝ,0 ≤ M → (∀ x∈Seed,‖F x‖ ≤ M) → ∀ x∈K,‖F x‖ ≤ C*M := by
  let Q:Set (R3×R3) := K\Seed
  have hQ:IsCompact Q := hK.diff hSeed
  choose ell rad hell hrad KS hKS hKSlevel hSmall Cpoint hCpoint H using fun p:Q =>
    hLocal p.val p.property.1 p.property.2
  have hMargins:∀ p:Q,∃ d:ℝ,0 < d ∧ ∀ y∈KS p,d ≤ level y-level p.val := by
    intro p
    apply exists_pos_margin_of_isCompact (hKS p)
    · exact (hLevel.mono (fun y hy => (hKSlevel p hy).1)).sub continuousOn_const
    · intro y hy
      exact sub_pos.mpr (hKSlevel p hy).2
  choose DP hDP HDP using hMargins
  have hRooms:∀ p:Q,∃ eps:ℝ,0 < eps ∧ ∀ x∈ball p.val eps,
      x∈ball p.val (rad p) ∧ level x < level p.val+DP p/2 := by
    intro p
    have hpU:p.val∈U := hKU p.property.1
    have hcont:ContinuousAt level p.val := hLevel.continuousAt (hU.mem_nhds hpU)
    have hpos:level p.val < level p.val+DP p/2 := by linarith only [hDP p]
    have hBallEvent:∀ᶠ x in 𝓝 p.val,x∈ball p.val (rad p) := isOpen_ball.mem_nhds (mem_ball_self (hrad p))
    have hev:∀ᶠ x in 𝓝 p.val,x∈ball p.val (rad p) ∧ level x < level p.val+DP p/2 :=
      hBallEvent.and (hcont.eventually (gt_mem_nhds hpos))
    obtain ⟨eps,heps,H⟩ := Metric.eventually_nhds_iff.mp hev
    exact ⟨eps,heps,fun x hx => H (mem_ball.mp hx)⟩
  choose eps heps HEps using hRooms
  have hCover:Q⊆⋃p:Q,ball p.val (eps p) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (heps ⟨x,hx⟩)⟩
  obtain ⟨t,ht⟩ := hQ.elim_finite_subcover (fun p:Q => ball p.val (eps p)) (fun _ => isOpen_ball) hCover
  have hFiniteLower:(∀ (f:Q→ℝ), (∀ p,0 < f p) → ∀ s:Finset Q,∃ l:ℝ,0 < l ∧ ∀ p∈s,l ≤ f p) := by
    intro f hf s
    induction s using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert p s hp ih =>
      obtain ⟨l,hl,Hl⟩ := ih
      refine ⟨min l (f p),lt_min hl (hf p),?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with heq | hq
      · subst q;exact min_le_right _ _
      · exact (min_le_left _ _).trans (Hl q hq)
  obtain ⟨lambda0,hlambda0,hLambda⟩ := hFiniteLower ell hell t
  obtain ⟨delta,hdelta,hDelta⟩ := hFiniteLower (fun p => DP p/2) (fun p => half_pos (hDP p)) t
  obtain ⟨B,hB⟩ := (t.finite_toSet.image Cpoint).bddAbove
  let A:ℝ := max B 1
  have hA:1 ≤ A := le_max_right _ _
  have hCpointA:∀ p∈t,Cpoint p ≤ A := fun p hp => (hB (Set.mem_image_of_mem _ hp)).trans (le_max_left _ _)
  obtain ⟨N,HN⟩ := exists_finite_level_budget_propagation K Seed level lo hi delta A hdelta hA hBand
  refine ⟨lambda0,A^N,hlambda0,pow_pos (zero_lt_one.trans_le hA) _,?_⟩
  intro L lambda hlam F hF M hM hSeedBound
  apply HN M hM (fun x => ‖F x‖) hSeedBound
  intro x hx hxSeed
  have hxQ:x∈Q := ⟨hx,hxSeed⟩
  obtain ⟨p,hp⟩ := Set.mem_iUnion.mp (ht hxQ)
  obtain ⟨hpt,hxp⟩ := Set.mem_iUnion.mp hp
  refine ⟨KS p,?_,?_⟩
  · intro y hy
    have hyU:y∈U := (hKSlevel p hy).1
    have hyLevel:lo ≤ level y := (hBand p.val p.property.1).1.trans (hKSlevel p hy).2.le
    rcases hHigh y hyU hyLevel with hySeed | hyK
    · exact Or.inl hySeed
    · refine Or.inr ⟨hyK,?_⟩
      have hSource:=HDP p y hy
      have hTarget:level x < level p.val+DP p/2 := (HEps p x hxp).2
      have hGain:delta ≤ DP p/2 := hDelta p hpt
      linarith only [hSource,hTarget,hGain]
  · intro T hT hBudget
    have hh:=H p L lambda ⟨hlam.1,hlam.2.trans (hLambda p hpt)⟩ F hF T hT hBudget x (HEps p x hxp).1
    exact hh.trans (mul_le_mul_of_nonneg_right (hCpointA p hpt) hT)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
