import Calderon.NativeValueRadialTrace
import Calderon.StrongHarmonicProjection

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge SphereHarmonic

theorem smoothSphereValue_testFunction_eq_zero (phi : 𝓓(ballOpens, ℝ)) :
    smoothSphereValue ⟨phi,phi.contDiff⟩ = 0 := by
  apply ContinuousMap.ext
  intro x
  change phi x.val = 0
  apply phi.zero_on_compl
  change x.val ∉ Metric.ball (0 : R3) 1
  intro hx
  have hn : ‖x.val‖ = 1 := by
    simpa [UnitSphere,Metric.sphere,dist_eq_norm] using x.property
  have hl : ‖x.val‖ < 1 := by simpa [Metric.mem_ball,dist_zero_right] using hx
  rw [hn] at hl
  exact lt_irrefl 1 hl

theorem valueTraceL_testFunction_eq_zero (τ0 : UnitBallValueTrace)
    (phi : 𝓓(ballOpens, ℝ)) : τ0.valueTraceL (testFunctionSobolev phi) = 0 := by
  rw [← smoothSobolev_testFunction phi,τ0.valueTrace_smooth,
    smoothSphereValue_testFunction_eq_zero,map_zero]

theorem valueTraceL_eq_zero_of_mem_w1p0 (τ0 : UnitBallValueTrace) (u : BallH1)
    (hu : u ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2) :
    τ0.valueTraceL u = 0 := by
  have hc : IsClosed {v : BallH1 | τ0.valueTraceL v = 0} :=
    isClosed_eq τ0.valueTraceL.continuous continuous_const
  have hsubset := TauCeti.w1p0Submodule_subset_of_isClosed
    (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) hc
    (fun phi => valueTraceL_testFunction_eq_zero τ0 phi)
  exact hsubset hu

theorem valueTraceL_zeroDirichlet (τ0 : UnitBallValueTrace) (u : BallH1Zero) :
    τ0.valueTraceL (u : BallH1) = 0 :=
  valueTraceL_eq_zero_of_mem_w1p0 τ0 u u.property

/-- The actual higher Sobolev value trace induced by the first-order trace. -/
def strongValueTraceL (τ0 : UnitBallValueTrace) (s : ℕ) :
    BallSobolev (s+2) →L[ℝ] SphereL2 :=
  τ0.valueTraceL.comp (TauCeti.Wkp.firstOrderL
    (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) (s+1))

theorem strongValueTraceL_apply (τ0 : UnitBallValueTrace) (s : ℕ)
    (u : BallSobolev (s+2)) :
    strongValueTraceL τ0 s u = τ0.valueTraceL (TauCeti.Wkp.firstOrder (s+1) u) := rfl

theorem strongValueTraceL_eq_zero_of_mem (τ0 : UnitBallValueTrace) (s : ℕ)
    (u : BallSobolev (s+2)) (hu : u ∈ strongDirichletSubmodule s) :
    strongValueTraceL τ0 s u = 0 := by
  rw [strongValueTraceL_apply]
  exact valueTraceL_eq_zero_of_mem_w1p0 τ0 _ ((mem_strongDirichletSubmodule s u).mp hu)

theorem strongValueTraceL_subtype (τ0 : UnitBallValueTrace) (s : ℕ)
    (u : StrongDirichletSpace s) : strongValueTraceL τ0 s (u : BallSobolev (s+2)) = 0 :=
  strongValueTraceL_eq_zero_of_mem τ0 s u u.property

theorem strongValueTraceL_smooth (τ0 : UnitBallValueTrace) (s : ℕ) (f : SmoothData) :
    strongValueTraceL τ0 s (smoothBallSobolev (s+2) f) =
      (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue f) := by
  rw [strongValueTraceL_apply,firstOrder_smoothBallSobolev (s+1) f,τ0.valueTrace_smooth]

theorem strongValueTraceL_eq_of_sub_mem (τ0 : UnitBallValueTrace) (s : ℕ)
    (u v : BallSobolev (s+2)) (huv : u-v ∈ strongDirichletSubmodule s) :
    strongValueTraceL τ0 s u = strongValueTraceL τ0 s v := by
  have hz := strongValueTraceL_eq_zero_of_mem τ0 s (u-v) huv
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

theorem strongValueTraceL_strongHarmonicProjection (τ0 : UnitBallValueTrace) (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s) (u : BallSobolev (s+2)) :
    strongValueTraceL τ0 s (strongHarmonicProjectionL s A u) =
      strongValueTraceL τ0 s u :=
  (strongValueTraceL_eq_of_sub_mem τ0 s u (strongHarmonicProjectionL s A u)
    (sub_strongHarmonicProjectionL_mem s A u)).symm

end OAI.AnisotropicCalderon.DirichletFamily
