import Calderon.RadiusTwoOffPoleDyadicCutoffChain
import Calderon.RadiusTwoCommonRowCutoffAllOrders
import Calderon.RadiusTwoNativeAllOrderCutoffLocalSmoothness

/-! EXPANSION.json and EXPANSION-local-identification.json precede SAME-row offpole smoothness. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution radiusTwoNativeZeroDilation

theorem contDiffOn_radiusTwoCommonRow_offpole_representative
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (G : R3 → ℝ)
    (hG : ContinuousOn G ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q}))
    (hGAE : G =ᵐ[(volume : Measure R3).restrict
      ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q})] (K : R3 → ℝ)) :
    ContDiffOn ℝ ∞ G ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q}) := by
  trace "PROOF ENTER actual SAME chosen-row offpole infinity"
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨ε,hε,C,hC,hCRoom,η,hEtaOne,hSupp,hChain,hBallRoom⟩ :=
    exists_radiusTwo_offpole_dyadic_cutoff_chain ((2 : ℝ) • q) x hx
  have hPole (j : ℕ) : (2 : ℝ) • q ∉ tsupport (η j : R3 → ℝ) := by
    intro hp
    exact (hCRoom (hSupp j hp)).2 (by simp)
  trace "FIXED DYADIC ROOM MADE actual SAME chosen-row offpole infinity"
  let P : (ℕ → RadiusTwoH1Zero) → Prop := fun w =>
    (∀ j : ℕ, (TauCeti.W1p.value (w j : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => η j z * K z)) ∧
    ∀ n j : ℕ, ∃ U : BallSobolev (n+1),
      TauCeti.Wkp.firstOrder n U = (radiusTwoNativeZeroDilation (w j) : BallH1)
  have hData : ∃ w : ℕ → RadiusTwoH1Zero, P w :=
    exists_radiusTwoCommonRow_cutoff_all_orders hreg hcalc g hg a ha ha1 q hq K hLimit
      η hPole hChain
  trace "ACTUAL ALL-ORDER CUTOFF PACKAGE MADE SAME chosen-row offpole infinity"
  refine Exists.elim hData ?_
  intro w hw
  have hLift (s : ℕ) : ∃ U : BallSobolev (s+2), TauCeti.Wkp.firstOrder (s+1) U =
      (radiusTwoNativeZeroDilation (w 0) : BallH1) := hw.2 (s+1) 0
  have hOpen : IsOpen ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q}) :=
    IsOpen.sdiff radiusTwoOpens.isOpen isClosed_singleton
  have hLocal : ∃ V : Set R3, IsOpen V ∧ x ∈ V ∧
      V ⊆ (radiusTwoOpens : Set R3) \ {(2 : ℝ) • q} ∧ ContDiffOn ℝ ∞ G V :=
    exists_contDiffOn_neighborhood_of_radiusTwoNativeAllOrder_cutoff hcalc K (w 0)
      (η 0 : R3 → ℝ) (hw.1 0) hLift G
      ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q}) hOpen hG hGAE
      x hx.1 hx ε hε (hEtaOne 0)
  trace "SAME SELECTED LOCAL SMOOTHNESS MADE actual chosen-row offpole infinity"
  refine Exists.elim hLocal ?_
  intro V hV
  exact ⟨V,hV.1,hV.2.1,(hV.2.2.2).mono inter_subset_right⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.contDiffOn_radiusTwoCommonRow_offpole_representative
