import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

private abbrev seminormedDomainClmNormedAddCommGroup (U F : Type*)
    [SeminormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (U →L[ℝ] F) :=
  NormedAddCommGroup.ofSeparation (fun (f : U →L[ℝ] F) (hf : ‖f‖ = 0) => by
    apply ContinuousLinearMap.ext
    intro u
    change f u = 0
    apply norm_le_zero_iff.mp
    calc
      ‖f u‖ ≤ ‖f‖ * ‖u‖ := f.le_opNorm u
      _ = 0 := by rw [hf, zero_mul])

attribute [local instance 50] seminormedDomainClmNormedAddCommGroup

theorem contDiff_finiteClmSandwichSeminormedDomain
    {X U H K ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [Fintype ι]
    (D : ι → U →L[ℝ] H) (P : ι → H →L[ℝ] K) (P0 : H →L[ℝ] K)
    (M : ι → ι → X → H →L[ℝ] H) (Mc : ι → X → H →L[ℝ] H)
    (hM : ∀ i j : ι, ContDiff ℝ ∞ (M i j))
    (hMc : ∀ i : ι, ContDiff ℝ ∞ (Mc i)) :
    ContDiff ℝ ∞ (fun p : X =>
      (∑ i : ι, ∑ j : ι, (P i).comp ((M i j p).comp (D j))) +
        ∑ i : ι, P0.comp ((Mc i p).comp (D i))) := by
  have hTerm (P1 : H →L[ℝ] K) (D1 : U →L[ℝ] H)
      (M1 : X → H →L[ℝ] H) (hM1 : ContDiff ℝ ∞ M1) :
      ContDiff ℝ ∞ (fun p : X => P1.comp ((M1 p).comp D1)) := by
    let T : (H →L[ℝ] H) →L[ℝ] U →L[ℝ] K :=
      (ContinuousLinearMap.compL ℝ U H K P1).comp
        ((ContinuousLinearMap.compL ℝ U H H).flip D1)
    have hT : ContDiff ℝ ∞ (fun p : X => T (M1 p)) := T.contDiff.comp hM1
    simpa only [T, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply] using hT
  exact (ContDiff.sum fun i hi => ContDiff.sum fun j hj =>
    hTerm (P i) (D j) (M i j) (hM i j)).add
      (ContDiff.sum fun i hi => hTerm P0 (D i) (Mc i) (hMc i))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
