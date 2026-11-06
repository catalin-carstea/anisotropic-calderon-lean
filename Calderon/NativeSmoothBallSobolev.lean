import Calderon.StrongDirichletDomain
import TauCeti.Analysis.Sobolev.Wkp.Zero
import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.Analysis.Sobolev.Wkp.Classical
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff Distributions Gradient Topology
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

/-- A fixed smooth cutoff for the actual Euclidean norm of `R3`. -/
def unitBallSmoothCutoff : ContDiffBump (0 : R3) where
  rIn := 2
  rOut := 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem unitBallSmoothCutoff_one_of_mem {x : R3} (hx : x ∈ ballOpens) :
    unitBallSmoothCutoff x = 1 := by
  apply unitBallSmoothCutoff.one_of_mem_closedBall
  change dist x (0 : R3) ≤ (2 : ℝ)
  change dist x (0 : R3) < (1 : ℝ) at hx
  linarith

theorem unitBallSmoothCutoff_eventuallyEq_one {x : R3}
    (hx : x ∈ Metric.closedBall (0 : R3) 1) :
    (unitBallSmoothCutoff : R3 → ℝ) =ᶠ[nhds x] (fun _ => 1) := by
  apply unitBallSmoothCutoff.eventuallyEq_one_of_mem_ball
  change dist x (0 : R3) < (2 : ℝ)
  change dist x (0 : R3) ≤ (1 : ℝ) at hx
  linarith

/-- The cutoff product is a genuine test function on the whole ambient space. -/
def smoothWholeSpaceTestFunction (f : SmoothData) : 𝓓((⊤ : Opens R3), ℝ) where
  toFun := fun x => unitBallSmoothCutoff x * f.1 x
  contDiff' := unitBallSmoothCutoff.contDiff.mul f.2
  hasCompactSupport' := by
    change HasCompactSupport ((unitBallSmoothCutoff : R3 → ℝ) * f.1)
    exact unitBallSmoothCutoff.hasCompactSupport.mul_right
  tsupport_subset' := by intro x hx; trivial

/-- The native Tau iterated weak-derivative graph element restricted to the exact ball. -/
def smoothBallSobolev (k : ℕ) (f : SmoothData) : BallSobolev k :=
  TauCeti.Wkp.restrictL (mu := (volume : Measure R3)) (p := 2)
    (le_top : ballOpens ≤ (⊤ : Opens R3)) k
    (TauCeti.Wkp.ofTestFunctionₗ (mu := (volume : Measure R3))
      (Omega := (⊤ : Opens R3)) (p := 2) k (smoothWholeSpaceTestFunction f))

theorem value_smoothBallSobolev_ae (k : ℕ) (f : SmoothData) :
    TauCeti.Wkp.value k (smoothBallSobolev k f)
      =ᵐ[(volume : Measure R3).restrict ballOpens] f.1 := by
  let phi : 𝓓((⊤ : Opens R3), ℝ) := smoothWholeSpaceTestFunction f
  let u : TauCeti.Wkp (volume : Measure R3) (⊤ : Opens R3) 2 k :=
    TauCeti.Wkp.ofTestFunctionₗ (mu := (volume : Measure R3))
      (Omega := (⊤ : Opens R3)) (p := 2) k phi
  have hu : TauCeti.Wkp.value k u
      =ᵐ[(volume : Measure R3).restrict (⊤ : Opens R3)] (phi : R3 → ℝ) := by
    dsimp only [u]
    rw [TauCeti.Wkp.value_ofTestFunctionₗ]
    exact TauCeti.testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 phi
  have hmeasure : (volume : Measure R3).restrict ballOpens ≤
      (volume : Measure R3).restrict (⊤ : Opens R3) :=
    Measure.restrict_mono_set volume
      (SetLike.coe_subset_coe.mpr (le_top : ballOpens ≤ (⊤ : Opens R3)))
  have huB := hu.filter_mono (MeasureTheory.ae_mono hmeasure)
  have hr := TauCeti.Wkp.value_restrictL_ae
    (mu := (volume : Measure R3)) (p := 2)
    (le_top : ballOpens ≤ (⊤ : Opens R3)) k u
  change TauCeti.Wkp.value k
    (TauCeti.Wkp.restrictL (mu := (volume : Measure R3)) (p := 2)
      (le_top : ballOpens ≤ (⊤ : Opens R3)) k u)
    =ᵐ[(volume : Measure R3).restrict ballOpens] f.1
  filter_upwards [hr, huB, ae_restrict_mem ballOpens.isOpen.measurableSet]
    with x hx hy hmem
  calc
    _ = phi x := hx.trans hy
    _ = f.1 x := by
      change unitBallSmoothCutoff x * f.1 x = f.1 x
      rw [unitBallSmoothCutoff_one_of_mem hmem, one_mul]

theorem value_smoothBallSobolev (k : ℕ) (f : SmoothData) :
    TauCeti.Wkp.value k (smoothBallSobolev k f) =
      (memLp_smooth_value f).toLp f.1 := by
  apply Lp.ext
  exact (value_smoothBallSobolev_ae k f).trans
    (MemLp.coeFn_toLp (memLp_smooth_value f)).symm

theorem firstOrder_smoothBallSobolev (k : ℕ) (f : SmoothData) :
    TauCeti.Wkp.firstOrder k (smoothBallSobolev (k + 1) f) =
      smoothSobolev f := by
  apply TauCeti.W1p.ext_value
  rw [TauCeti.Wkp.value_firstOrder, value_smoothBallSobolev, value_smoothSobolev]

theorem lowerOrder_smoothBallSobolev (k : ℕ) (f : SmoothData) :
    TauCeti.Wkp.lowerOrder k (smoothBallSobolev (k + 1) f) =
      smoothBallSobolev k f := by
  apply TauCeti.Wkp.ext k
  rw [← TauCeti.Wkp.value_succ k (smoothBallSobolev (k + 1) f),
    value_smoothBallSobolev, value_smoothBallSobolev]

theorem iteratedGradient_smoothBallSobolev_ae (k : ℕ) (f : SmoothData) :
    TauCeti.Wkp.iteratedGradient k (smoothBallSobolev (k + 1) f)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
      TauCeti.iteratedGradientChain f.1 k := by
  exact TauCeti.Wkp.iteratedGradient_ae_eq_of_contDiffOn k
    (smoothBallSobolev (k + 1) f) ((f.2.of_le (by simp)).contDiffOn)
    (value_smoothBallSobolev_ae (k + 1) f)

/-- Restriction uses the actual native iterated graph norm. -/
theorem norm_smoothBallSobolev_le_wholeSpace (k : ℕ) (f : SmoothData) :
    ‖smoothBallSobolev k f‖ ≤
      ‖TauCeti.Wkp.ofTestFunctionₗ (mu := (volume : Measure R3))
        (Omega := (⊤ : Opens R3)) (p := 2) k (smoothWholeSpaceTestFunction f)‖ := by
  exact TauCeti.Wkp.norm_restrictL_le
    (mu := (volume : Measure R3)) (p := 2)
    (le_top : ballOpens ≤ (⊤ : Opens R3)) k
    (TauCeti.Wkp.ofTestFunctionₗ (mu := (volume : Measure R3))
      (Omega := (⊤ : Opens R3)) (p := 2) k (smoothWholeSpaceTestFunction f))

end OAI.AnisotropicCalderon.DirichletFamily
