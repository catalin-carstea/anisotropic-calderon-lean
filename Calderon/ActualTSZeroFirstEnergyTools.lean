import Calderon.ActualTSSymmetricFirstGreen
import Calderon.ActualTSFirstLinearZeroIntegral

/-! Elementary energy and integral bookkeeping for the literal original D01.
No final analytic cap is assumed here; actual original-room producers discharge these interfaces. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstEnergyTools
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFiniteHarmonicCore ActualFullEGainedAssembly ActualFullEGainedEndpoints
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth NormalizedPrincipalMetric
  PrincipalCommutator ActualHigherSScalarCommutatorForm
  ActualHigherSScalarCommutatorNativeForm ActualHigherSZeroScalarCommutatorForm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Green pairing for a Hi-valued input and its continuous dual. -/
def evaluationPairing : E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.apply ℝ ℝ

theorem evaluationPairing_apply (u : E) (l : E →L[ℝ] ℝ) :
    evaluationPairing u l = l u := rfl

/-- The original mass term is bounded by the unchanged inclusion energy. -/
theorem inclusion_mass_le (I : E →L[ℝ] F) (beta : ℝ) (u : R3 → E)
    (x : R3) (hb : 0 ≤ beta) :
    beta*‖u x‖^2 ≤ inclusionEnergyDensity I beta u x := by
  unfold inclusionEnergyDensity
  exact le_add_of_nonneg_left (mul_nonneg (inv_nonneg.mpr hb)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- All integrals exist before a pointwise remainder bound is integrated. -/
theorem weighted_integral_abs_le_of_pointwise
    (mu f e : R3 → ℝ) (A : ℝ) (hmu : ∀ x, 0 ≤ mu x)
    (hf : Integrable (fun x => mu x*f x))
    (he : Integrable (fun x => mu x*e x))
    (hpoint : ∀ x, |f x| ≤ A*e x) :
    |∫ x, mu x*f x| ≤ A*∫ x, mu x*e x := by
  have hAbs : Integrable (fun x => |mu x*f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  calc
    _ ≤ ∫ x, |mu x*f x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, A*(mu x*e x) := by
      apply integral_mono hAbs (he.const_mul A)
      intro x
      change |mu x*f x| ≤ A*(mu x*e x)
      rw [abs_mul,abs_of_nonneg (hmu x)]
      exact (mul_le_mul_of_nonneg_left (hpoint x) (hmu x)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

/-- A finite family uses every original occurrence, with no cancellation assumed. -/
theorem abs_integral_finite_sum_le {ι : Type*} [Fintype ι]
    (f : ι → R3 → ℝ) (C energy : ℝ)
    (hf : ∀ i, Integrable (f i))
    (hcap : ∀ i, |∫ x, f i x| ≤ C*energy) :
    |∫ x, ∑ i, f i x| ≤ (Fintype.card ι : ℝ)*C*energy := by
  rw [integral_finset_sum Finset.univ (fun i _ => hf i)]
  calc
    _ ≤ ∑ i, |∫ x, f i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, C*energy := Finset.sum_le_sum (fun i _ => hcap i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

/-- Operator-norm pairing bound used by the full original raw correction. -/
theorem abs_bilinear_actions_le
    (P : E →L[ℝ] F →L[ℝ] ℝ)
    {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : H →L[ℝ] E) (B : G →L[ℝ] F) (u : H) (v : G)
    (CA CB : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hA : ‖A‖ ≤ CA) (hB : ‖B‖ ≤ CB) :
    |P (A u) (B v)| ≤ ‖P‖*CA*CB*‖u‖*‖v‖ := by
  have hAu : ‖A u‖ ≤ CA*‖u‖ :=
    (A.le_opNorm u).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg u))
  have hBv : ‖B v‖ ≤ CB*‖v‖ :=
    (B.le_opNorm v).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg v))
  have hPair : |P (A u) (B v)| ≤ ‖P‖*‖A u‖*‖B v‖ := by
    simpa only [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm₂ P (A u) (B v)
  exact (hPair.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hAu (norm_nonneg P)) hBv (norm_nonneg _)
    (mul_nonneg (norm_nonneg P) (mul_nonneg hCA (norm_nonneg u))))).trans_eq (by ring)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstEnergyTools
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstEnergyTools.abs_integral_finite_sum_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstEnergyTools.abs_bilinear_actions_le
