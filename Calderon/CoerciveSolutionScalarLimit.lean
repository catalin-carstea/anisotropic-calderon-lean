import Calderon.CoerciveSolutionScalarEstimate
import Calderon.ScalarStabilityCurveHeader
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Filter
open scoped Topology
namespace OAI.AnisotropicCalderon.DirichletFamily

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem tendsto_solution_of_scalar_energy_rhs_limits
    {I : Type*} (l : Filter I) (B : I → V →L[ℝ] StrongDual ℝ V)
    (C : V →L[ℝ] StrongDual ℝ V) (hC : IsCoercive C)
    (ell : I → StrongDual ℝ V) (ell0 : StrongDual ℝ V) (z : I → V) (z0 : V)
    (hB : Tendsto B l (𝓝 C)) (hEll : Tendsto ell l (𝓝 ell0))
    (hz : ∀ i : I, ∀ v : V, B i (z i) v = ell i v)
    (hz0 : ∀ v : V, C z0 v = ell0 v) : Tendsto z l (𝓝 z0) := by
  obtain ⟨c,hc,hBound⟩ := hC
  have hBound' : ∀ v : V, c*‖v‖^2 ≤ C v v := by
    intro v
    simpa only [pow_two,mul_assoc] using hBound v
  have hBDiff : Tendsto (fun i => ‖B i-C‖) l (𝓝 (0 : ℝ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hB
  have hEllDiff : Tendsto (fun i => ‖ell i-ell0‖) l (𝓝 (0 : ℝ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hEll
  have hControl : Tendsto (fun i => (2/c)*(‖ell i-ell0‖+‖B i-C‖*‖z0‖))
      l (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul,zero_add,mul_zero] using
      (hEllDiff.add (hBDiff.mul_const ‖z0‖)).const_mul (2/c)
  have hSmall : ∀ᶠ i in l, ‖B i-C‖ ≤ c/2 := by
    have h := hBDiff.eventually (Iio_mem_nhds (show (0 : ℝ) < c/2 by linarith))
    exact h.mono (fun i hi => le_of_lt hi)
  have hNormBound : ∀ᶠ i in l,
      ‖z i-z0‖ ≤ (2/c)*(‖ell i-ell0‖+‖B i-C‖*‖z0‖) :=
    hSmall.mono (fun i hi => norm_solution_sub_le_of_scalar_coercivity
      (B i) C c hc hBound' hi (ell i) ell0 (z i) z0 (hz i) hz0)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hNormBound hControl)


end OAI.AnisotropicCalderon.DirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.tendsto_solution_of_scalar_energy_rhs_limits
