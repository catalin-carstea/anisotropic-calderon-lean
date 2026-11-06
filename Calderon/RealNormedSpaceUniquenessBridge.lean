import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Author diagnostic, 28 October 2026. No replacement structures or instances.
For one fixed NormedAddCommGroup, two real NormedSpace structures coincide:
the continuous additive identity is real linear. This proof never unfolds
any concrete NormedSpace value. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

private lemma normedSpace_eq_of_module_eq
    {E : Type*} [NormedAddCommGroup E]
    (s t : NormedSpace ℝ E) (h : s.toModule = t.toModule) : s = t := by
  cases s
  cases t
  cases h
  rfl

lemma real_normedSpace_eq
    {E : Type*} [NormedAddCommGroup E]
    (s t : NormedSpace ℝ E) : s = t := by
  have hs : (letI := s; ContinuousSMul ℝ E) := by
    letI := s
    infer_instance
  have ht : (letI := t; ContinuousSMul ℝ E) := by
    letI := t
    infer_instance
  apply normedSpace_eq_of_module_eq
  apply Module.ext'
  intro c x
  exact @map_real_smul E _ s.toModule _ hs E _ t.toModule _ ht _
    (E →+ E) _ _ (AddMonoidHom.id E) continuous_id c x

lemma contDiff_real_normedSpace_iff
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] (s t : NormedSpace ℝ E) (f : P → E) :
    (letI := s; ContDiff ℝ ∞ f) ↔ (letI := t; ContDiff ℝ ∞ f) := by
  cases real_normedSpace_eq s t
  rfl

lemma contDiffAt_real_normedSpace_iff
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] (s t : NormedSpace ℝ E) (f : P → E) (p : P) :
    (letI := s; ContDiffAt ℝ ∞ f p) ↔ (letI := t; ContDiffAt ℝ ∞ f p) := by
  cases real_normedSpace_eq s t
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
