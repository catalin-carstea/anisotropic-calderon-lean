import Calderon.NativeSupportedAdjointWeakSolution
import Calderon.StrongDirichletDomain
import Calderon.ParametricWeightedForcing

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! The strong space is the existing actual H2 domain with precisely first-order zero boundary. -/

lemma exists_continuousLinearMap_of_bounded_solve
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : X →L[ℝ] Y) (hQ : Function.Injective Q) (F : Z →L[ℝ] Y)
    (C : ℝ) (hC : 0 ≤ C)
    (hSolve : ∀ f : Z, ∃ u : X, Q u = F f ∧ ‖u‖ ≤ C*‖f‖) :
    ∃ R : Z →L[ℝ] X, Q.comp R = F ∧ ‖R‖ ≤ C := by
  classical
  let U : Z → X := fun f => Classical.choose (hSolve f)
  have hU : ∀ f, Q (U f) = F f := fun f => (Classical.choose_spec (hSolve f)).1
  have hBound : ∀ f, ‖U f‖ ≤ C*‖f‖ := fun f => (Classical.choose_spec (hSolve f)).2
  let L : Z →ₗ[ℝ] X :=
    { toFun := U
      map_add' := fun f g => hQ (by rw [hU,Q.map_add,hU,hU,F.map_add])
      map_smul' := fun c f => hQ (by rw [hU,Q.map_smul,hU,F.map_smul]; rfl) }
  let R : Z →L[ℝ] X := L.mkContinuous C hBound
  refine ⟨R,?_,LinearMap.mkContinuous_norm_le L hC hBound⟩
  apply ContinuousLinearMap.ext
  intro f
  exact hU f

def nativeDirichletForcingL : BallSobolev 0 →L[ℝ] StrongDual ℝ BallH1Zero := by
  have hg := forcingFromValueL (V := BallH1Zero) (H := BallSobolev 0)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hg
  exact hg (TauCeti.W1p0.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2))

lemma nativeDirichletForcingL_apply (f : BallSobolev 0) :
    nativeDirichletForcingL f =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f := rfl

attribute [local irreducible] nativeZeroCoefficientEnergyL nativeDirichletForcingL

lemma nativeZeroCoefficientEnergyL_isWeakSolution_iff (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (f : BallSobolev 0) (u : BallH1Zero) :
    TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens) a b c f u ↔
      nativeZeroCoefficientEnergyL a b c hcoeff u = nativeDirichletForcingL f := by
  have he : ∀ v : BallH1Zero,
      nativeZeroCoefficientEnergyL a b c hcoeff u v =
        TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
          a b c (u : BallH1) (v : BallH1) := fun v =>
    nativeZeroCoefficientEnergyL_eval_to_H1 a b c hcoeff u v
  constructor
  · intro hu
    apply ContinuousLinearMap.ext
    intro v
    exact (he v).trans ((hu v).trans
      (congrArg (fun ell : StrongDual ℝ BallH1Zero => ell v) (nativeDirichletForcingL_apply f)).symm)
  · intro hu v
    have hv := congrArg (fun ell : StrongDual ℝ BallH1Zero => ell v) hu
    exact (he v).symm.trans (hv.trans
      (congrArg (fun ell : StrongDual ℝ BallH1Zero => ell v) (nativeDirichletForcingL_apply f)))

def nativeStrongH2Representative (u : BallH1Zero) (U : BallSobolev 2)
    (hU : TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1 U =
      (u : BallH1)) : StrongDirichletSpace 0 :=
  ⟨U,by
    change TauCeti.Wkp.firstOrder 1 U ∈ TauCeti.w1p0Submodule volume ballOpens 2
    exact hU.symm ▸ u.2⟩

lemma nativeStrongH2Representative_projection (u : BallH1Zero) (U : BallSobolev 2)
    (hU : TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1 U =
      (u : BallH1)) : strongDirichletProjectionL 0 (nativeStrongH2Representative u U hU) = u := by
  apply Subtype.ext
  exact (strongDirichletProjectionL_apply 0 (nativeStrongH2Representative u U hU)).trans hU

lemma norm_nativeStrongH2Representative (u : BallH1Zero) (U : BallSobolev 2)
    (hU : TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1 U =
      (u : BallH1)) : ‖nativeStrongH2Representative u U hU‖ = ‖U‖ := rfl

attribute [local irreducible] nativeStrongH2Representative

lemma exists_nativeZeroStrong_bounded_solve_of_eval
    (A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
    (Weak : BallSobolev 0 → BallH1Zero → Prop)
    (hEval : ∀ (f : BallSobolev 0) (u : BallH1Zero), Weak f u → A u = nativeDirichletForcingL f)
    (C : ℝ) (hSolve : ∀ f : BallSobolev 0, ∃ (u : BallH1Zero) (U : BallSobolev 2),
      Weak f u ∧ TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) 1 U = (u : BallH1) ∧ ‖U‖ ≤ C*‖f‖) :
    ∀ f : BallSobolev 0, ∃ V : StrongDirichletSpace 0,
      (A.comp (strongDirichletProjectionL 0)) V = nativeDirichletForcingL f ∧ ‖V‖ ≤ C*‖f‖ := by
  intro f
  exact Exists.elim (hSolve f)
    (fun (u : BallH1Zero)
      (hu : ∃ U : BallSobolev 2, Weak f u ∧
        TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) 1 U = (u : BallH1) ∧ ‖U‖ ≤ C*‖f‖) =>
      Exists.elim hu (fun (U : BallSobolev 2)
        (h : Weak f u ∧ TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) 1 U = (u : BallH1) ∧ ‖U‖ ≤ C*‖f‖) =>
        let hw : Weak f u := And.left h
        let hU : TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
            (p := 2) 1 U = (u : BallH1) := And.left (And.right h)
        let hBound : ‖U‖ ≤ C*‖f‖ := And.right (And.right h)
        ⟨nativeStrongH2Representative u U hU,
          (congrArg A (nativeStrongH2Representative_projection u U hU)).trans (hEval f u hw),
          (norm_nativeStrongH2Representative u U hU).trans_le hBound⟩))

lemma exists_native_zeroStrong_bounded_solve (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (C : ℝ)
    (hSolve : ∀ f : BallSobolev 0, ∃ (u : BallH1Zero) (U : BallSobolev 2),
      TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens) a b c f u ∧
      TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) 1 U = (u : BallH1) ∧ ‖U‖ ≤ C*‖f‖) :
    ∀ f : BallSobolev 0, ∃ V : StrongDirichletSpace 0,
      ((nativeZeroCoefficientEnergyL a b c hcoeff).comp (strongDirichletProjectionL 0)) V =
        nativeDirichletForcingL f ∧ ‖V‖ ≤ C*‖f‖ := by
  exact exists_nativeZeroStrong_bounded_solve_of_eval
    (nativeZeroCoefficientEnergyL a b c hcoeff)
    (TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens) a b c)
    (fun f u hu => (nativeZeroCoefficientEnergyL_isWeakSolution_iff a b c hcoeff f u).mp hu) C hSolve

lemma exists_nativeStrong_solutionCLM_of_bounded_solve
    (A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) (hA : A.IsInvertible)
    (Weak : BallSobolev 0 → BallH1Zero → Prop)
    (hEval : ∀ (f : BallSobolev 0) (u : BallH1Zero), Weak f u ↔ A u = nativeDirichletForcingL f)
    (hSolve : ∃ D : ℝ, 0 ≤ D ∧ ∀ f : BallSobolev 0, ∃ (u : BallH1Zero) (U : BallSobolev 2),
      Weak f u ∧ TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) 1 U = (u : BallH1) ∧ ‖U‖ ≤ D*‖f‖) :
    ∃ R : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0,
      ∀ f : BallSobolev 0, Weak f (strongDirichletProjectionL 0 (R f)) := by
  obtain ⟨D,hD,hSol⟩ := hSolve
  have hs := exists_nativeZeroStrong_bounded_solve_of_eval A Weak
    (fun f u hu => (hEval f u).mp hu) D hSol
  have hQ : Function.Injective (A.comp (strongDirichletProjectionL 0)) :=
    hA.injective.comp (strongDirichletProjectionL_injective 0)
  have hg := exists_continuousLinearMap_of_bounded_solve (X := StrongDirichletSpace 0)
    (Y := StrongDual ℝ BallH1Zero) (Z := BallSobolev 0)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hg
  obtain ⟨R,hR,hNorm⟩ := hg (A.comp (strongDirichletProjectionL 0)) hQ nativeDirichletForcingL D hD hs
  refine ⟨R,?_⟩
  intro f
  apply (hEval f (strongDirichletProjectionL 0 (R f))).mpr
  exact congrArg (fun T : BallSobolev 0 →L[ℝ] StrongDual ℝ BallH1Zero => T f) hR


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_continuousLinearMap_of_bounded_solve
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeDirichletForcingL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeDirichletForcingL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroCoefficientEnergyL_isWeakSolution_iff
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeStrongH2Representative
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeStrongH2Representative_projection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_nativeStrongH2Representative
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeZeroStrong_bounded_solve_of_eval
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_native_zeroStrong_bounded_solve
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeStrong_solutionCLM_of_bounded_solve
