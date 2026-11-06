import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-! Full upfront expansion: EXPANSION-sphere-sobolev-full-rotation-orbit-derivative-v001.json. -/

lemma tendstoUniformly_contractive_family_apply
    {E F A N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : A → E →L[ℝ] F) (hT : ∀ x v, ‖T x v‖ ≤ ‖v‖)
    (u : N → E) (v : E) (l : Filter N) (hu : Tendsto u l (𝓝 v)) :
    TendstoUniformly (fun n x => T x (u n)) (fun x => T x v) l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hv := Metric.tendsto_nhds.mp hu ε hε
  filter_upwards [hv] with n hn
  intro x
  rw [dist_eq_norm,← map_sub]
  have hn' : ‖v-u n‖ < ε :=
    lt_of_eq_of_lt (norm_sub_rev v (u n)) (by simpa only [dist_eq_norm] using hn)
  exact (hT x (v-u n)).trans_lt hn'

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tendstoUniformly_contractive_family_apply
