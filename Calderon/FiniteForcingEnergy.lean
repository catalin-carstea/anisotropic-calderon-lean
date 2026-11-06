import Calderon.ParametricWeightedForcing
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily

/-! Abstract finite real-Hilbert energy evaluation and opnorm parameter
composition. All three complete contracts were sealed before these bodies.
No actual energy, PDE regularity or physical-family conclusion is assumed. -/


theorem forcingFromValueL_apply_apply
    {V H : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (j : V →L[ℝ] H) (f : H) (v : V) :
    forcingFromValueL j f v = ⟪f, j v⟫_ℝ := by
  simp only [forcingFromValueL_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]

theorem finiteForcingEnergy_apply
    {U V H ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype ι]
    (J : V →L[ℝ] U) (D : ι → U →L[ℝ] H) (value : U →L[ℝ] H)
    (M : ι → ι → H →L[ℝ] H) (Mc : ι → H →L[ℝ] H) (u : U) (v : V) :
    ((∑ i : ι, ∑ j : ι,
      (forcingFromValueL ((D i).comp J)).comp ((M i j).comp (D j))) +
      ∑ i : ι, (forcingFromValueL (value.comp J)).comp ((Mc i).comp (D i))) u v =
      (∑ i : ι, ∑ j : ι, ⟪M i j (D j u), D i (J v)⟫_ℝ) +
        ∑ i : ι, ⟪Mc i (D i u), value (J v)⟫_ℝ := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, forcingFromValueL_apply_apply]

private abbrev strongDualNormedAddCommGroup (V : Type*)
    [SeminormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (StrongDual ℝ V) :=
  NormedAddCommGroup.ofSeparation (fun (f : StrongDual ℝ V) (hf : ‖f‖ = 0) => by
    apply ContinuousLinearMap.ext
    intro v
    change f v = 0
    apply norm_le_zero_iff.mp
    calc
      ‖f v‖ ≤ ‖f‖ * ‖v‖ := f.le_opNorm v
      _ = 0 := by rw [hf, zero_mul])

attribute [local instance] strongDualNormedAddCommGroup

theorem contDiff_finiteForcingEnergy
    {X U V H ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype ι]
    (J : V →L[ℝ] U) (D : ι → U →L[ℝ] H) (value : U →L[ℝ] H)
    (M : ι → ι → X → H →L[ℝ] H) (Mc : ι → X → H →L[ℝ] H)
    (hM : ∀ i j : ι, ContDiff ℝ ∞ (M i j))
    (hMc : ∀ i : ι, ContDiff ℝ ∞ (Mc i)) :
    ContDiff ℝ ∞ (fun p : X =>
      (∑ i : ι, ∑ j : ι,
        (forcingFromValueL ((D i).comp J)).comp ((M i j p).comp (D j))) +
        ∑ i : ι, (forcingFromValueL (value.comp J)).comp ((Mc i p).comp (D i))) := by
  have hPrincipal (i j : ι) : ContDiff ℝ ∞ (fun p : X =>
      (forcingFromValueL ((D i).comp J)).comp ((M i j p).comp (D j))) :=
    contDiff_const.clm_comp ((hM i j).clm_comp contDiff_const)
  have hDrift (i : ι) : ContDiff ℝ ∞ (fun p : X =>
      (forcingFromValueL (value.comp J)).comp ((Mc i p).comp (D i))) :=
    contDiff_const.clm_comp ((hMc i).clm_comp contDiff_const)
  exact (ContDiff.sum fun i hi => ContDiff.sum fun j hj => hPrincipal i j).add
    (ContDiff.sum fun i hi => hDrift i)

end OAI.AnisotropicCalderon.DirichletFamily
