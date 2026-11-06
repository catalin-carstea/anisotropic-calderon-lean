import Calderon.UnitBallValueTraceKernel
import Calderon.CollaboratorTraceKernelHelpersOct17
import Calderon.CollaboratorSmoothDensityBallOct17

/-! The kernel of the value trace is `H¹₀(B)`.

`(⇐)`: test-function jets are jets of globally smooth functions vanishing on the sphere, so the
trace vanishes on them; the kernel is closed.

`(⇒)`: for smooth `f`, a radial cutoff and a boundary-layer Hardy estimate in polar coordinates
(`TraceKernel.infDist_sq_le_smooth`) give
`dist(f, H¹₀)² ≤ K_ε ‖τ f‖² + C ‖∇f‖²_{L²(layer ε)}` with `C` independent of `ε`.  By density of
smooth jets and continuity this holds for all `u`; for `τ u = 0` let `ε → 0`. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Filter Topology
open scoped Distributions
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge TraceKernel

theorem ofTestFunction_eq_smoothSobolev (φ : 𝓓(ballOpens, ℝ)) :
    TauCeti.W1p.ofTestFunctionₗ (volume : Measure R3) ballOpens 2 φ =
      smoothSobolev ⟨(φ : R3 → ℝ), φ.contDiff⟩ := by
  apply TauCeti.W1p.ext_value
  rw [TauCeti.W1p.value_ofTestFunctionₗ]
  apply Lp.ext
  filter_upwards [TauCeti.testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 φ,
    value_smoothSobolev_ae ⟨(φ : R3 → ℝ), φ.contDiff⟩] with x h1 h2
  rw [h1, h2]

theorem trace_testFunction (τ0 : UnitBallValueTrace) (φ : 𝓓(ballOpens, ℝ)) :
    τ0.valueTraceL (TauCeti.W1p.ofTestFunctionₗ (volume : Measure R3) ballOpens 2 φ) = 0 := by
  rw [ofTestFunction_eq_smoothSobolev, τ0.valueTrace_smooth]
  have h0 : smoothSphereValue ⟨(φ : R3 → ℝ), φ.contDiff⟩ = 0 := by
    ext w
    have hw : (w : R3) ∉ (ballOpens : Set R3) := by
      simp [B, norm_eq_of_mem_sphere w]
    exact φ.zero_on_compl hw
  rw [h0, map_zero]

theorem unitBallValueTraceKernel (τ0 : UnitBallValueTrace) : UnitBallValueTraceKernel τ0 := by
  intro u
  set H0 : Set BallH1 := (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 : Set BallH1)
    with hH0
  constructor
  · intro hu
    obtain ⟨C, hC⟩ := infDist_sq_le_smooth τ0
    have hgen : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        Metric.infDist u H0 ^ 2 ≤ C * ‖layerGrad ε u‖ ^ 2 := by
      intro ε hε0 hε
      obtain ⟨K, hK⟩ := hC ε hε0 hε
      obtain ⟨f, hf⟩ := exists_smoothSobolev_tendsto u
      have hcont : Continuous fun v : BallH1 =>
          K * ‖τ0.valueTraceL v‖ ^ 2 + C * ‖layerGrad ε v‖ ^ 2 - Metric.infDist v H0 ^ 2 := by
        have h1 := τ0.valueTraceL.continuous
        have h2 := (layerGrad ε).continuous
        have h3 : Continuous fun v : BallH1 => Metric.infDist v H0 :=
          Metric.continuous_infDist_pt H0
        fun_prop
      have hge := ge_of_tendsto ((hcont.tendsto u).comp hf)
        (Eventually.of_forall fun n => sub_nonneg.2 (hK (f n)))
      rw [hu] at hge
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_add, sub_nonneg] at hge
      exact hge
    have hlim := (tendsto_norm_sq_layerGrad u).const_mul C
    rw [mul_zero] at hlim
    have hle : Metric.infDist u H0 ^ 2 ≤ 0 :=
      ge_of_tendsto' hlim fun (n : ℕ) => hgen (1 / ((n : ℝ) + 2)) (by positivity)
        (one_div_le_one_div_of_le (by norm_num) (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]))
    have hzero : Metric.infDist u H0 = 0 := by nlinarith [Metric.infDist_nonneg (x := u) (s := H0)]
    have hclosed : IsClosed H0 := (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).isClosed
    exact (hclosed.mem_iff_infDist_zero ⟨0, Submodule.zero_mem _⟩).2 hzero
  · intro hu
    exact TauCeti.w1p0Submodule_subset_of_isClosed (s := {v : BallH1 | τ0.valueTraceL v = 0})
      (isClosed_eq τ0.valueTraceL.continuous continuous_const)
      (fun φ => trace_testFunction τ0 φ) hu

end OAI.AnisotropicCalderon.DirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.unitBallValueTraceKernel
