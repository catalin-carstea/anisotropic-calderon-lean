import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Calderon.MixedRadialJetCalculus

/-! UNCOMPILED author proposal. EXPANSION.md L1--L3 was saved before this source. -/
set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem continuousAt_parameterJetField_of_contDiffAt (j : ℕ) (F : P × ℝ → V)
    (x : P × ℝ) (hF : ContDiffAt ℝ ∞ F x) :
    ContinuousAt (parameterJetField j F) x := by
  unfold parameterJetField
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin j => ContinuousLinearMap.inl ℝ P ℝ)).continuous.continuousAt.comp
      (hF.differentiableAt_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top j)).continuousAt

theorem parameterJetField_eq_of_eventuallyEq (j : ℕ) (F G : P × ℝ → V)
    (x : P × ℝ) (heq : F =ᶠ[𝓝 x] G) :
    parameterJetField j F x = parameterJetField j G x := by
  unfold parameterJetField
  rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]

theorem parameterJetField_eq_on_set_of_local_eq (j : ℕ) (F G : P × ℝ → V)
    (s t : Set P) (hst : s ⊆ t) (hts : t ⊆ closure s) (r : ℝ)
    (hF : ∀ p ∈ t, ContDiffAt ℝ ∞ F (p,r))
    (hG : ∀ p ∈ t, ContDiffAt ℝ ∞ G (p,r))
    (heq : ∀ p ∈ s, F =ᶠ[𝓝 (p,r)] G) :
    ∀ p ∈ t, parameterJetField j F (p,r) = parameterJetField j G (p,r) := by
  have hlocal : EqOn (fun p => parameterJetField j F (p,r))
      (fun p => parameterJetField j G (p,r)) s := by
    intro p hp
    exact parameterJetField_eq_of_eventuallyEq j F G (p,r) (heq p hp)
  have hcF : ContinuousOn (fun p => parameterJetField j F (p,r)) t := by
    intro p hp
    exact ((continuousAt_parameterJetField_of_contDiffAt j F (p,r) (hF p hp)).comp (f := fun z : P => (z,r)) (x := p)
      (show ContinuousAt (fun z : P => (z,r)) p from
        continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  have hcG : ContinuousOn (fun p => parameterJetField j G (p,r)) t := by
    intro p hp
    exact ((continuousAt_parameterJetField_of_contDiffAt j G (p,r) (hG p hp)).comp (f := fun z : P => (z,r)) (x := p)
      (show ContinuousAt (fun z : P => (z,r)) p from
        continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  exact hlocal.of_subset_closure hcF hcG hst hts

end OAI.AnisotropicCalderon.ConnectionError
