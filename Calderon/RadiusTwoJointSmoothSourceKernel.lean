import Calderon.RadiusTwoSmoothRowSpanWordEvaluations
import Calderon.RadiusTwoLocalSmoothPoleWordYFamily
import Calderon.RadiusTwoCompactPoleCutoffRoom
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets
attribute [local instance] Classical.propDecidable

theorem contDiffAt_radiusTwo_sourceKernel_offDiagonal
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (p₀ z₀ : (radiusTwoOpens : Set R3)) (hNe : (p₀ : R3) ≠ (z₀ : R3)) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (fun v : R3 × R3 =>
      if hp : v.1 ∈ (radiusTwoOpens : Set R3) then G ⟨v.1,hp⟩ v.2 else 0)
      ((p₀ : R3),(z₀ : R3)) := by
  classical
  have hzOff : (z₀ : R3) ∈ (radiusTwoOpens : Set R3) \ {(p₀ : R3)} := by
    refine ⟨z₀.property,?_⟩
    intro h
    exact hNe (mem_singleton_iff.mp h).symm
  have hCut := exists_radiusTwo_compactPole_dyadic_cutoff_room
    ({(p₀ : R3)} : Set R3) isCompact_singleton (z₀ : R3) hzOff
  rcases hCut with ⟨s,hs,η,hRoom,hEta,hSupp,hOne,hAvoid,hInner⟩
  let S : Set R3 := closedBall (z₀ : R3) s
  let Z : Set R3 := ball (z₀ : R3) (s/2)
  have hS : IsCompact S := isCompact_closedBall (z₀ : R3) s
  have hSB : S ⊆ (radiusTwoOpens : Set R3) := fun z hz => (hRoom hz).1
  have hSN : S.Nonempty := ⟨z₀,mem_closedBall_self hs.le⟩
  have hpOff : (p₀ : R3) ∈ (radiusTwoOpens : Set R3) \ S := by
    refine ⟨p₀.property,?_⟩
    intro h
    exact (hRoom h).2 (by simp)
  obtain ⟨zMax,hzMax,hMax⟩ := hS.exists_isMaxOn hSN continuous_norm.continuousOn
  have hm : ‖zMax‖ < 2 := by
    have h := hSB hzMax
    change zMax ∈ ball (0 : R3) 2 at h
    simpa only [mem_ball,dist_zero_right] using h
  let a₀ : ℝ := (‖zMax‖+2)/4
  have ha₀ : 0 < a₀ := by dsimp only [a₀]; nlinarith [norm_nonneg zMax]
  have ha₀1 : a₀ < 1 := by dsimp only [a₀]; linarith
  have hZS : Z ⊆ S := by
    intro z hz
    exact closedBall_subset_closedBall (by linarith : s/2 ≤ s) (ball_subset_closedBall hz)
  have hSInner : S ⊆ ball (0 : R3) (2*a₀) := by
    intro z hz
    have h := hMax hz
    change ‖z‖ ≤ ‖zMax‖ at h
    rw [mem_ball,dist_zero_right]
    dsimp only [a₀]
    linarith
  have hZInner : Z ⊆ ball (0 : R3) (2*a₀) := fun z hz => hSInner (hZS hz)
  have hPoleFamily := exists_radiusTwo_local_smooth_poleWord_Y_family
    hreg hcalc g hg K G hData S hS hSB (p₀ : R3) hpOff
  rcases hPoleFamily with ⟨r,hr,hClosed,M,hM,hWords,hPoleFamily⟩
  let ν : Measure R3 := ((volume : Measure R3).restrict radiusTwoOpens).restrict S
  let O : Set R3 := ball (p₀ : R3) (r/2)
  let hOB : O ⊆ (radiusTwoOpens : Set R3) \ S := fun p hp =>
    hClosed (closedBall_subset_closedBall (by linarith : r/2 ≤ r) (ball_subset_closedBall hp))
  let R : RadiusTwoL2 →L[ℝ] Lp ℝ 2 ν := MeasureTheory.LpToLpRestrictCLM R3 ℝ ℝ
    ((volume : Measure R3).restrict radiusTwoOpens) 2 S
  let F : O → Lp ℝ 2 ν := fun p => R (K ⟨p,(hOB p.property).1⟩)
  let Y : Submodule ℝ (Lp ℝ 2 ν) := (Submodule.span ℝ (Set.range F)).topologicalClosure
  rcases hPoleFamily with ⟨D,hD,hBase,hSmoothY,hRestricted,hJets⟩
  let F₀ : R3 → Y := fun q => if hq : q ∈ O then D ⟨q,hq⟩ [] else 0
  have hF₀ : ContDiffOn ℝ (∞ : ℕ∞ω) F₀ O := hSmoothY []
  let liftRows : O → Y := fun p => ⟨F p,
    (Submodule.le_topologicalClosure _)
      (Submodule.subset_span (show F p ∈ Set.range F from ⟨p,rfl⟩))⟩
  have hYValue (p : O) : F₀ p = liftRows p := by
    apply Subtype.ext
    simpa only [F₀,dif_pos p.property,liftRows] using hBase p
  have hDualFamily := exists_radiusTwo_smooth_rowSpan_word_evaluations
    hreg hcalc g hg K G hData η S hS.measurableSet hSupp hOne O hOB
    a₀ ha₀ ha₀1 Z isOpen_ball (convex_ball _ _) hZInner (fun z hz => hEta 0 z hz)
  rcases hDualFamily with ⟨C,hC,L,hStatic,hSmoothL,hDerivL⟩
  have hFst : ContDiffOn ℝ (∞ : ℕ∞ω) (fun v : R3 × R3 => F₀ v.1) (O ×ˢ Z) :=
    hF₀.comp contDiffOn_fst (fun v hv => hv.1)
  have hSnd : ContDiffOn ℝ (∞ : ℕ∞ω) (fun v : R3 × R3 => L [] v.2) (O ×ˢ Z) :=
    (hSmoothL []).comp contDiffOn_snd (fun v hv => hv.2)
  have hJoint : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun v : R3 × R3 => L [] v.2 (F₀ v.1)) (O ×ˢ Z) :=
    hSnd.clm_apply hFst
  have hActual : ContDiffOn ℝ (∞ : ℕ∞ω) (fun v : R3 × R3 =>
      if hp : v.1 ∈ (radiusTwoOpens : Set R3) then G ⟨v.1,hp⟩ v.2 else 0) (O ×ˢ Z) := by
    apply hJoint.congr
    intro v hv
    rw [dif_pos (hOB hv.1).1]
    have hGenerator := (hStatic [] v.2 hv.2).2.2.1 ⟨v.1,hv.1⟩
    have hRow := hYValue ⟨v.1,hv.1⟩
    exact ((congrArg (fun u : Y => L [] v.2 u) hRow).trans hGenerator).symm
  have hOpen : IsOpen (O ×ˢ Z) := isOpen_ball.prod isOpen_ball
  have hCenter : ((p₀ : R3),(z₀ : R3)) ∈ O ×ˢ Z :=
    ⟨mem_ball_self (by linarith),mem_ball_self (by linarith)⟩
  exact hActual.contDiffAt (hOpen.mem_nhds hCenter)

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.contDiffAt_radiusTwo_sourceKernel_offDiagonal
