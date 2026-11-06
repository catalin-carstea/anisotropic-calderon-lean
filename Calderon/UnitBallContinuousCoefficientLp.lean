import Calderon.NativeWeightedDriftFluxGreen
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.CompactOpen

/-! EXPANSION.json precedes this exact complete generic Energy13 partition.
Six original mathematical constructs are preserved byte-for-byte. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set Filter
open scoped ENNReal Matrix.Norms.Elementwise ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

abbrev UnitClosedBall := {x : R3 // x ∈ Metric.closedBall (0 : R3) 1}

local instance : CompactSpace UnitClosedBall :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : R3) 1)

section ContinuousField
variable {V : Type*} [NormedAddCommGroup V]

def unitBallContinuousFieldLp (H : ℝ → R3 → V)
    (hH : Continuous (fun p : ℝ × R3 => H p.1 p.2)) (R : ℝ) :
    Lp V ⊤ ((volume : Measure R3).restrict ballOpens) :=
  (memLp_unitBall_of_continuous_normed (H R)
    (hH.comp (continuous_const.prodMk continuous_id))).toLp (H R)

def unitClosedBallField (H : ℝ → R3 → V)
    (hH : Continuous (fun p : ℝ × R3 => H p.1 p.2)) (R : ℝ) : C(UnitClosedBall, V) :=
  ⟨fun x => H R x.val,
    hH.comp (continuous_const.prodMk continuous_subtype_val)⟩

theorem continuous_unitClosedBallField (H : ℝ → R3 → V)
    (hH : Continuous (fun p : ℝ × R3 => H p.1 p.2)) :
    Continuous (unitClosedBallField H hH) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hH.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

theorem norm_unitBallContinuousFieldLp_sub_le (H : ℝ → R3 → V)
    (hH : Continuous (fun p : ℝ × R3 => H p.1 p.2)) (R S : ℝ) :
    ‖unitBallContinuousFieldLp H hH R - unitBallContinuousFieldLp H hH S‖ ≤
      ‖unitClosedBallField H hH R - unitClosedBallField H hH S‖ := by
  let μ : Measure R3 := (volume : Measure R3).restrict ballOpens
  letI : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ, coe_ballOpens] using
      ((measure_mono (show B ⊆ Metric.closedBall (0 : R3) 1 from Metric.ball_subset_closedBall)).trans_lt
        (isCompact_closedBall (0 : R3) 1).measure_lt_top)⟩
  have hR : unitBallContinuousFieldLp H hH R =ᵐ[μ] H R :=
    MemLp.coeFn_toLp _
  have hS : unitBallContinuousFieldLp H hH S =ᵐ[μ] H S :=
    MemLp.coeFn_toLp _
  have hsub : ⇑(unitBallContinuousFieldLp H hH R - unitBallContinuousFieldLp H hH S) =ᵐ[μ]
      (fun x => H R x - H S x) :=
    (Lp.coeFn_sub _ _).trans (hR.sub hS)
  have hb : ∀ᵐ x ∂μ,
      ‖(unitBallContinuousFieldLp H hH R - unitBallContinuousFieldLp H hH S) x‖ ≤
        ‖unitClosedBallField H hH R - unitClosedBallField H hH S‖ := by
    filter_upwards [hsub, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
    rw [hx]
    exact (unitClosedBallField H hH R - unitClosedBallField H hH S).norm_coe_le_norm
      ⟨x, Metric.ball_subset_closedBall hxB⟩
  simpa using Lp.norm_le_of_ae_bound
    (norm_nonneg (unitClosedBallField H hH R - unitClosedBallField H hH S)) hb

theorem continuous_unitBallContinuousFieldLp (H : ℝ → R3 → V)
    (hH : Continuous (fun p : ℝ × R3 => H p.1 p.2)) :
    Continuous (unitBallContinuousFieldLp H hH) := by
  apply continuous_iff_continuousAt.mpr
  intro R
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousAt_iff.mp
    (continuous_unitClosedBallField H hH).continuousAt ε hε
  refine ⟨δ, hδ, ?_⟩
  intro S hS
  rw [dist_eq_norm]
  exact (norm_unitBallContinuousFieldLp_sub_le H hH S R).trans_lt
    (by simpa only [dist_eq_norm] using hbound hS)

end ContinuousField

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.UnitClosedBall
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.unitBallContinuousFieldLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.unitClosedBallField
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_unitClosedBallField
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_unitBallContinuousFieldLp_sub_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_unitBallContinuousFieldLp
