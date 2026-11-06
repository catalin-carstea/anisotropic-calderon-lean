import Calderon.PrincipalDirectional
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Operations
noncomputable section
set_option autoImplicit false
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCubicProductDerivative
open PrincipalCommutator
variable {E H N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

@[instance_reducible, instance] def fullCubicDerivativeOperatorNorm :
    Norm (R3 →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) where
  norm T := ContinuousLinearMap.opNorm
    (E := R3) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ) T

lemma fullCubicDerivativeOperatorNorm_norm_def
    (T : R3 →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    @Norm.norm _ (fullCubicDerivativeOperatorNorm (E := E)) T =
      ContinuousLinearMap.opNorm
        (E := R3) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ) T := rfl

private lemma fullCubicDerivative_opNorm_le_bound
    (T : R3 →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hT : ∀ X : R3, ‖T X‖ ≤ C0*‖X‖) : ‖T‖ ≤ C0 := by
  have h := ContinuousLinearMap.opNorm_le_bound
    (E := R3) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq, normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at h
  exact h T hC0 hT

private lemma forms_differentiableAt_add
    (f g : R3 → E →L[ℝ] E →L[ℝ] ℝ) (x : R3)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => f y+g y) x := by
  have h := DifferentiableAt.add (𝕜 := ℝ) (E := R3) (F := E →L[ℝ] E →L[ℝ] ℝ)
    (f := f) (g := g) (x := x)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq, normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at h
  exact h hf hg

private lemma forms_fderiv_add
    (f g : R3 → E →L[ℝ] E →L[ℝ] ℝ) (x : R3)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun y => f y+g y) x=fderiv ℝ f x+fderiv ℝ g x := by
  have h := fderiv_fun_add (𝕜 := ℝ) (E := R3) (F := E →L[ℝ] E →L[ℝ] ℝ)
    (f := f) (g := g) (x := x)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq, normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at h
  exact h hf hg

private lemma r3_addCommGroup_eq :
    (inferInstance : NormedAddCommGroup R3).toAddCommGroup =
      (inferInstance : AddCommGroup R3) := rfl
private lemma r3_module_eq :
    (inferInstance : NormedSpace ℝ R3).toModule =
      (inferInstance : Module ℝ R3) := rfl
private lemma r3_topologicalSpace_eq :
    (inferInstance : NormedAddCommGroup R3).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace R3) := rfl

private lemma forms_isBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) := by
  have h := NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq, normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at h
  exact h

private lemma forms_norm_smul (c : ℝ) (T : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖c • T‖=|c| *‖T‖ := by
  have h := NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq, normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at h
  letI : NormSMulClass ℝ (E →L[ℝ] E →L[ℝ] ℝ) := h
  simpa only [Real.norm_eq_abs] using norm_smul c T

private lemma forms_fderiv_smul
    (s : R3 → ℝ) (f : R3 → E →L[ℝ] E →L[ℝ] ℝ) (x : R3)
    (hs : DifferentiableAt ℝ s x) (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => s y • f y) x=
      s x • fderiv ℝ f x+(fderiv ℝ s x).smulRight (f x) := by
  letI : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) := forms_isBoundedSMul
  have h := fderiv_fun_smul (𝕜 := ℝ) (E := R3) (F := E →L[ℝ] E →L[ℝ] ℝ)
    (c := s) (f := f) (x := x)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq, normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at h
  exact h hs hf

def cubicForm (P : H →L[ℝ] N →L[ℝ] ℝ) (A C : E →L[ℝ] H) (B : H →L[ℝ] N) : E →L[ℝ] E →L[ℝ] ℝ :=
  P.bilinearComp A (B.comp C)
def cubicDerivative (P : H →L[ℝ] N →L[ℝ] ℝ)
    (A C dA dC : E →L[ℝ] H) (B dB : H →L[ℝ] N) : E →L[ℝ] E →L[ℝ] ℝ :=
  cubicForm P dA C B+cubicForm P A C dB+cubicForm P A dC B

def pairedCubicForm (P : H →L[ℝ] N →L[ℝ] ℝ)
    (A1 C1 A2 C2 : E →L[ℝ] H) (B1 B2 : H →L[ℝ] N) : E →L[ℝ] E →L[ℝ] ℝ :=
  cubicForm P A1 C1 B1+cubicForm P A2 C2 B2

private lemma directional_clm_apply_at {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : R3 → V →L[ℝ] W) (v : R3 → V) (x X : R3)
    (hT : DifferentiableAt ℝ T x) (hv : DifferentiableAt ℝ v x) :
    directionalFDeriv X (fun y => T y (v y)) x=
      T x (directionalFDeriv X v x)+(directionalFDeriv X T x) (v x) := by
  unfold directionalFDeriv
  rw [fderiv_clm_apply hT hv]
  rfl

private lemma directional_apply_const {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : R3 → V →L[ℝ] W) (v : V) (x X : R3) (hT : DifferentiableAt ℝ T x) :
    directionalFDeriv X (fun y => T y v) x=(directionalFDeriv X T x) v := by
  have h := directional_clm_apply_at T (fun _ => v) x X hT (differentiableAt_const v)
  simpa only [directionalFDeriv,fderiv_const_apply,zero_apply,map_zero,zero_add] using h

private lemma directional_fixed_linear {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : V →L[ℝ] W) (v : R3 → V) (x X : R3) (hv : DifferentiableAt ℝ v x) :
    directionalFDeriv X (fun y => T (v y)) x=T (directionalFDeriv X v x) := by
  have h := T.hasFDerivAt.comp x hv.hasFDerivAt
  change (fderiv ℝ (T ∘ v) x) X=T ((fderiv ℝ v x) X)
  rw [h.fderiv]
  rfl

private lemma norm_cubicForm_le (P : H →L[ℝ] N →L[ℝ] ℝ)
    (A C : E →L[ℝ] H) (B : H →L[ℝ] N) :
    ‖cubicForm P A C B‖ ≤ ‖P‖*‖A‖*‖B‖*‖C‖ := by
  calc
    _ = ‖((P.comp A).flip).comp (B.comp C)‖ := by
      unfold cubicForm ContinuousLinearMap.bilinearComp
      rw [ContinuousLinearMap.opNorm_flip]
    _ ≤ ‖(P.comp A).flip‖*‖B.comp C‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖P.comp A‖*‖B.comp C‖ := by rw [ContinuousLinearMap.opNorm_flip]
    _ ≤ (‖P‖*‖A‖)*(‖B‖*‖C‖) := mul_le_mul
      (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
      (norm_nonneg _) (by positivity)
    _ = _ := by ring

private lemma norm_cubicForm_of_caps (P : H →L[ℝ] N →L[ℝ] ℝ)
    (A C : E →L[ℝ] H) (B : H →L[ℝ] N) (MA MC MB : ℝ)
    (hMA : 0 ≤ MA) (hMC : 0 ≤ MC) (hMB : 0 ≤ MB)
    (hA : ‖A‖ ≤ MA) (hC : ‖C‖ ≤ MC) (hB : ‖B‖ ≤ MB) :
    ‖cubicForm P A C B‖ ≤ ‖P‖*MA*MB*MC := by
  exact (norm_cubicForm_le P A C B).trans (by gcongr)

private lemma norm_cubicDerivative_le (P : H →L[ℝ] N →L[ℝ] ℝ)
    (A C dA dC : E →L[ℝ] H) (B dB : H →L[ℝ] N) (M M1 : ℝ)
    (hM : 0 ≤ M) (hM1 : 0 ≤ M1)
    (hA : ‖A‖ ≤ M) (hC : ‖C‖ ≤ M) (hB : ‖B‖ ≤ M)
    (hdA : ‖dA‖ ≤ M1) (hdC : ‖dC‖ ≤ M1) (hdB : ‖dB‖ ≤ M1) :
    ‖cubicDerivative P A C dA dC B dB‖ ≤ 3*‖P‖*M^2*M1 := by
  have h1 := norm_cubicForm_of_caps P dA C B M1 M M hM1 hM hM hdA hC hB
  have h2 := norm_cubicForm_of_caps P A C dB M M M1 hM hM hM1 hA hC hdB
  have h3 := norm_cubicForm_of_caps P A dC B M M1 M hM hM1 hM hA hdC hB
  unfold cubicDerivative
  calc
    _ ≤ (‖cubicForm P dA C B‖+‖cubicForm P A C dB‖)+‖cubicForm P A dC B‖ :=
      (norm_add_le (cubicForm P dA C B+cubicForm P A C dB) (cubicForm P A dC B)).trans
        (add_le_add (norm_add_le (cubicForm P dA C B) (cubicForm P A C dB))
          (le_refl ‖cubicForm P A dC B‖))
    _ ≤ (‖P‖*M1*M*M+‖P‖*M*M1*M)+‖P‖*M*M*M1 := add_le_add (add_le_add h1 h2) h3
    _ = 3*‖P‖*M^2*M1 := by ring

theorem differentiableAt_cubicForm (P : H →L[ℝ] N →L[ℝ] ℝ)
    (A C : R3 → E →L[ℝ] H) (B : R3 → H →L[ℝ] N) (x : R3)
    (hA : DifferentiableAt ℝ A x) (hC : DifferentiableAt ℝ C x) (hB : DifferentiableAt ℝ B x) :
    DifferentiableAt ℝ (fun y => cubicForm P (A y) (C y) (B y)) x := by
  let F1 : (E →L[ℝ] N →L[ℝ] ℝ) →L[ℝ] N →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ E N ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let F2 : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hF1apply (T : E →L[ℝ] N →L[ℝ] ℝ) : F1 T=T.flip := by
    change (ContinuousLinearMap.flipₗᵢ ℝ E N ℝ) T=T.flip
    exact congrFun (ContinuousLinearMap.coe_flipₗᵢ (𝕜 := ℝ) (E := E) (Fₗ := N) (Gₗ := ℝ)) T
  have hF2apply (T : E →L[ℝ] E →L[ℝ] ℝ) : F2 T=T.flip := by
    change (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ) T=T.flip
    exact congrFun (ContinuousLinearMap.coe_flipₗᵢ (𝕜 := ℝ) (E := E) (Fₗ := E) (Gₗ := ℝ)) T
  have hPA : DifferentiableAt ℝ (fun y => P.comp (A y)) x :=
    (differentiableAt_const P).clm_comp hA
  have hLin1 := ContinuousLinearMap.differentiableAt (𝕜 := ℝ)
    (E := E →L[ℝ] N →L[ℝ] ℝ) (F := N →L[ℝ] E →L[ℝ] ℝ) (x := P.comp (A x))
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq, normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hLin1
  have hF1 : DifferentiableAt ℝ
      (fun T : E →L[ℝ] N →L[ℝ] ℝ => F1 T) (P.comp (A x)) := hLin1 F1
  have hCompose1 := DifferentiableAt.comp (𝕜 := ℝ) (E := R3)
    (F := E →L[ℝ] N →L[ℝ] ℝ) (G := N →L[ℝ] E →L[ℝ] ℝ)
    (f := fun y : R3 => P.comp (A y)) (g := fun T => F1 T) x
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq, normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq,
    r3_addCommGroup_eq, r3_module_eq, r3_topologicalSpace_eq] at hCompose1
  have hComposed := hCompose1 hF1 hPA
  have hFlipFn : ((fun T : E →L[ℝ] N →L[ℝ] ℝ => F1 T) ∘
      (fun y : R3 => P.comp (A y)))=(fun y : R3 => (P.comp (A y)).flip) := by
    funext y
    exact hF1apply (P.comp (A y))
  have hFlip : DifferentiableAt ℝ (fun y : R3 => (P.comp (A y)).flip) x := by
    rw [hFlipFn] at hComposed
    exact hComposed
  have hBC : DifferentiableAt ℝ (fun y : R3 => (B y).comp (C y)) x := hB.clm_comp hC
  have hMid : DifferentiableAt ℝ
      (fun y : R3 => ((P.comp (A y)).flip).comp ((B y).comp (C y))) x := hFlip.clm_comp hBC
  have hLin2 := ContinuousLinearMap.differentiableAt (𝕜 := ℝ)
    (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (x := ((P.comp (A x)).flip).comp ((B x).comp (C x)))
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq, normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hLin2
  have hF2 : DifferentiableAt ℝ
      (fun T : E →L[ℝ] E →L[ℝ] ℝ => F2 T)
      (((P.comp (A x)).flip).comp ((B x).comp (C x))) := hLin2 F2
  have hCompose2 := DifferentiableAt.comp (𝕜 := ℝ) (E := R3)
    (F := E →L[ℝ] E →L[ℝ] ℝ) (G := E →L[ℝ] E →L[ℝ] ℝ)
    (f := fun y : R3 => ((P.comp (A y)).flip).comp ((B y).comp (C y)))
    (g := fun T => F2 T) x
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq, normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq,
    r3_addCommGroup_eq, r3_module_eq, r3_topologicalSpace_eq] at hCompose2
  have hDone := hCompose2 hF2 hMid
  have hDoneFn : ((fun T : E →L[ℝ] E →L[ℝ] ℝ => F2 T) ∘
      (fun y : R3 => ((P.comp (A y)).flip).comp ((B y).comp (C y))))=
      (fun y : R3 => cubicForm P (A y) (C y) (B y)) := by
    funext y
    exact hF2apply (((P.comp (A y)).flip).comp ((B y).comp (C y)))
  rw [hDoneFn] at hDone
  exact hDone

theorem contDiffAt_cubicForm (P : H →L[ℝ] N →L[ℝ] ℝ)
    (A C : R3 → E →L[ℝ] H) (B : R3 → H →L[ℝ] N) (x : R3)
    (hA : ContDiffAt ℝ ∞ A x) (hC : ContDiffAt ℝ ∞ C x) (hB : ContDiffAt ℝ ∞ B x) :
    ContDiffAt ℝ ∞ (fun y => cubicForm P (A y) (C y) (B y)) x := by
  let F1 : (E →L[ℝ] N →L[ℝ] ℝ) →L[ℝ] N →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ E N ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let F2 : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hF1apply (T : E →L[ℝ] N →L[ℝ] ℝ) : F1 T=T.flip := by
    change (ContinuousLinearMap.flipₗᵢ ℝ E N ℝ) T=T.flip
    exact congrFun (ContinuousLinearMap.coe_flipₗᵢ (𝕜 := ℝ) (E := E) (Fₗ := N) (Gₗ := ℝ)) T
  have hF2apply (T : E →L[ℝ] E →L[ℝ] ℝ) : F2 T=T.flip := by
    change (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ) T=T.flip
    exact congrFun (ContinuousLinearMap.coe_flipₗᵢ (𝕜 := ℝ) (E := E) (Fₗ := E) (Gₗ := ℝ)) T
  have hPA : ContDiffAt ℝ ∞ (fun y => P.comp (A y)) x := contDiffAt_const.clm_comp hA
  have hLin1 := ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := E →L[ℝ] N →L[ℝ] ℝ) (F := N →L[ℝ] E →L[ℝ] ℝ) (n := ∞)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq, normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hLin1
  have hF1 : ContDiffAt ℝ ∞
      (fun T : E →L[ℝ] N →L[ℝ] ℝ => F1 T) (P.comp (A x)) := (hLin1 F1).contDiffAt
  have hComposed := hF1.comp x hPA
  have hFlipFn : ((fun T : E →L[ℝ] N →L[ℝ] ℝ => F1 T) ∘
      (fun y : R3 => P.comp (A y)))=(fun y : R3 => (P.comp (A y)).flip) := by
    funext y
    exact hF1apply (P.comp (A y))
  have hFlip : ContDiffAt ℝ ∞ (fun y : R3 => (P.comp (A y)).flip) x := by
    rw [hFlipFn] at hComposed
    exact hComposed
  have hBC : ContDiffAt ℝ ∞ (fun y : R3 => (B y).comp (C y)) x := hB.clm_comp hC
  have hMid : ContDiffAt ℝ ∞
      (fun y : R3 => ((P.comp (A y)).flip).comp ((B y).comp (C y))) x := hFlip.clm_comp hBC
  have hLin2 := ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (n := ∞)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq, normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hLin2
  have hF2 : ContDiffAt ℝ ∞
      (fun T : E →L[ℝ] E →L[ℝ] ℝ => F2 T)
      (((P.comp (A x)).flip).comp ((B x).comp (C x))) := (hLin2 F2).contDiffAt
  have hDone := hF2.comp x hMid
  have hDoneFn : ((fun T : E →L[ℝ] E →L[ℝ] ℝ => F2 T) ∘
      (fun y : R3 => ((P.comp (A y)).flip).comp ((B y).comp (C y))))=
      (fun y : R3 => cubicForm P (A y) (C y) (B y)) := by
    funext y
    exact hF2apply (((P.comp (A y)).flip).comp ((B y).comp (C y)))
  rw [hDoneFn] at hDone
  exact hDone

theorem directional_cubicForm (P : H →L[ℝ] N →L[ℝ] ℝ)
    (A C : R3 → E →L[ℝ] H) (B : R3 → H →L[ℝ] N) (x X : R3)
    (hA : DifferentiableAt ℝ A x) (hC : DifferentiableAt ℝ C x) (hB : DifferentiableAt ℝ B x) :
    directionalFDeriv X (fun y => cubicForm P (A y) (C y) (B y)) x=
      cubicDerivative P (A x) (C x) (directionalFDeriv X A x) (directionalFDeriv X C x)
        (B x) (directionalFDeriv X B x) := by
  let Q := fun y => cubicForm P (A y) (C y) (B y)
  have hQ := differentiableAt_cubicForm P A C B x hA hC hB
  ext v w
  have hQv : DifferentiableAt ℝ (fun y => Q y v) x := hQ.clm_apply (differentiableAt_const v)
  have hEval : (directionalFDeriv X Q x) v w=
      directionalFDeriv X (fun y => Q y v w) x := by
    calc
      _ = (directionalFDeriv X (fun y => Q y v) x) w :=
        congrArg (fun T : E →L[ℝ] ℝ => T w) (directional_apply_const Q v x X hQ).symm
      _ = _ := (directional_apply_const (fun y => Q y v) w x X hQv).symm
  have hAv : DifferentiableAt ℝ (fun y => A y v) x := hA.clm_apply (differentiableAt_const v)
  have hCw : DifferentiableAt ℝ (fun y => C y w) x := hC.clm_apply (differentiableAt_const w)
  have hBCw : DifferentiableAt ℝ (fun y => B y (C y w)) x := hB.clm_apply hCw
  have hPAv : DifferentiableAt ℝ (fun y => P (A y v)) x := P.differentiableAt.comp x hAv
  have hScalar := directional_clm_apply_at (fun y => P (A y v)) (fun y => B y (C y w)) x X hPAv hBCw
  have hDInner := directional_clm_apply_at B (fun y => C y w) x X hB hCw
  have hDLeft := directional_fixed_linear P (fun y => A y v) x X hAv
  rw [hDInner,hDLeft,directional_apply_const A v x X hA,directional_apply_const C w x X hC] at hScalar
  simp only [map_add] at hScalar
  exact hEval.trans (hScalar.trans (by
    simp only [cubicDerivative,cubicForm,ContinuousLinearMap.add_apply,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply]
    abel))

private lemma norm_fderiv_cubicForm_le (P : H →L[ℝ] N →L[ℝ] ℝ)
    (A C : R3 → E →L[ℝ] H) (B : R3 → H →L[ℝ] N) (x : R3)
    (hA : DifferentiableAt ℝ A x) (hC : DifferentiableAt ℝ C x) (hB : DifferentiableAt ℝ B x)
    (M M1 : ℝ) (hM : 0 ≤ M) (hM1 : 0 ≤ M1)
    (hAv : ‖A x‖ ≤ M) (hCv : ‖C x‖ ≤ M) (hBv : ‖B x‖ ≤ M)
    (hAd : ‖fderiv ℝ A x‖ ≤ M1) (hCd : ‖fderiv ℝ C x‖ ≤ M1) (hBd : ‖fderiv ℝ B x‖ ≤ M1) :
    ‖(fderiv ℝ (fun y : R3 => cubicForm P (A y) (C y) (B y)) x : R3 →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)‖ ≤ 3*‖P‖*M^2*M1 := by
  refine fullCubicDerivative_opNorm_le_bound _ _ (by positivity) (fun X => ?_)
  have hDA : ‖directionalFDeriv X A x‖ ≤ M1*‖X‖ :=
    ((fderiv ℝ A x).le_opNorm X).trans (mul_le_mul_of_nonneg_right hAd (norm_nonneg X))
  have hDC : ‖directionalFDeriv X C x‖ ≤ M1*‖X‖ :=
    ((fderiv ℝ C x).le_opNorm X).trans (mul_le_mul_of_nonneg_right hCd (norm_nonneg X))
  have hDB : ‖directionalFDeriv X B x‖ ≤ M1*‖X‖ :=
    ((fderiv ℝ B x).le_opNorm X).trans (mul_le_mul_of_nonneg_right hBd (norm_nonneg X))
  change ‖directionalFDeriv X (fun y => cubicForm P (A y) (C y) (B y)) x‖ ≤ _
  rw [directional_cubicForm P A C B x X hA hC hB]
  exact (norm_cubicDerivative_le P (A x) (C x) _ _ (B x) _ M (M1*‖X‖)
    hM (mul_nonneg hM1 (norm_nonneg _)) hAv hCv hBv hDA hDC hDB).trans (le_of_eq (by ring))

variable (P : H →L[ℝ] N →L[ℝ] ℝ)
  (A1 C1 A2 C2 : R3 → E →L[ℝ] H) (B1 B2 : R3 → H →L[ℝ] N) (x X : R3)
  (hA1 : DifferentiableAt ℝ A1 x) (hC1 : DifferentiableAt ℝ C1 x)
  (hA2 : DifferentiableAt ℝ A2 x) (hC2 : DifferentiableAt ℝ C2 x)
  (hB1 : DifferentiableAt ℝ B1 x) (hB2 : DifferentiableAt ℝ B2 x)
local notation "Q" => fun y => pairedCubicForm P (A1 y) (C1 y) (A2 y) (C2 y) (B1 y) (B2 y)
local notation "DQ" => cubicDerivative P (A1 x) (C1 x) (directionalFDeriv X A1 x) (directionalFDeriv X C1 x)
  (B1 x) (directionalFDeriv X B1 x)+
  cubicDerivative P (A2 x) (C2 x) (directionalFDeriv X A2 x) (directionalFDeriv X C2 x)
  (B2 x) (directionalFDeriv X B2 x)

include hA1 hC1 hA2 hC2 hB1 hB2

theorem directional_pairedCubicForm : directionalFDeriv X Q x=DQ := by
  have hQ1 := differentiableAt_cubicForm P A1 C1 B1 x hA1 hC1 hB1
  have hQ2 := differentiableAt_cubicForm P A2 C2 B2 x hA2 hC2 hB2
  have hAdd : fderiv ℝ (fun y : R3 => cubicForm P (A1 y) (C1 y) (B1 y)+
      cubicForm P (A2 y) (C2 y) (B2 y)) x =
      fderiv ℝ (fun y : R3 => cubicForm P (A1 y) (C1 y) (B1 y)) x+
      fderiv ℝ (fun y : R3 => cubicForm P (A2 y) (C2 y) (B2 y)) x :=
    forms_fderiv_add _ _ x hQ1 hQ2
  change (fderiv ℝ (fun y : R3 => cubicForm P (A1 y) (C1 y) (B1 y)+
    cubicForm P (A2 y) (C2 y) (B2 y)) x) X=_
  rw [hAdd]
  change directionalFDeriv X (fun y => cubicForm P (A1 y) (C1 y) (B1 y)) x+
    directionalFDeriv X (fun y => cubicForm P (A2 y) (C2 y) (B2 y)) x=_
  rw [directional_cubicForm P A1 C1 B1 x X hA1 hC1 hB1,
    directional_cubicForm P A2 C2 B2 x X hA2 hC2 hB2]

theorem directional_weightedPairedCubicForm (s : R3 → ℝ) (hs : DifferentiableAt ℝ s x) :
    directionalFDeriv X (fun y => s y • Q y) x=
      directionalFDeriv X s x • Q x+s x • DQ := by
  have hQ1 : DifferentiableAt ℝ (fun y : R3 => cubicForm P (A1 y) (C1 y) (B1 y)) x :=
    differentiableAt_cubicForm P A1 C1 B1 x hA1 hC1 hB1
  have hQ2 : DifferentiableAt ℝ (fun y : R3 => cubicForm P (A2 y) (C2 y) (B2 y)) x :=
    differentiableAt_cubicForm P A2 C2 B2 x hA2 hC2 hB2
  have hQ : DifferentiableAt ℝ Q x := by
    change DifferentiableAt ℝ (fun y => cubicForm P (A1 y) (C1 y) (B1 y)+
      cubicForm P (A2 y) (C2 y) (B2 y)) x
    exact forms_differentiableAt_add _ _ x hQ1 hQ2
  change (fderiv ℝ (fun y => s y • Q y) x) X=_
  rw [forms_fderiv_smul s Q x hs hQ]
  change s x • directionalFDeriv X Q x+directionalFDeriv X s x • Q x=_
  rw [directional_pairedCubicForm P A1 C1 A2 C2 B1 B2 x X hA1 hC1 hA2 hC2 hB1 hB2]
  abel

theorem directional_weightedPairedCubicForm_apply (s : R3 → ℝ) (hs : DifferentiableAt ℝ s x) (U : E) :
    directionalFDeriv X (fun y => s y • Q y) x U U=
      directionalFDeriv X s x*(P (A1 x U) (B1 x (C1 x U))+P (A2 x U) (B2 x (C2 x U)))+
      s x*(P (directionalFDeriv X A1 x U) (B1 x (C1 x U))+
        P (A1 x U) (directionalFDeriv X B1 x (C1 x U))+
        P (A1 x U) (B1 x (directionalFDeriv X C1 x U))+
        (P (directionalFDeriv X A2 x U) (B2 x (C2 x U))+
        P (A2 x U) (directionalFDeriv X B2 x (C2 x U))+
        P (A2 x U) (B2 x (directionalFDeriv X C2 x U)))) := by
  have h := congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T U U)
    (directional_weightedPairedCubicForm P A1 C1 A2 C2 B1 B2 x X hA1 hC1 hA2 hC2 hB1 hB2 s hs)
  simpa only [pairedCubicForm,cubicDerivative,cubicForm,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply,smul_eq_mul] using h

omit hA1 hC1 hA2 hC2 hB1 hB2 in
theorem norm_pairedCubicForm_le (M : ℝ) (hM : 0 ≤ M)
    (hAv1 : ‖A1 x‖ ≤ M) (hCv1 : ‖C1 x‖ ≤ M) (hAv2 : ‖A2 x‖ ≤ M) (hCv2 : ‖C2 x‖ ≤ M)
    (hBv1 : ‖B1 x‖ ≤ M) (hBv2 : ‖B2 x‖ ≤ M) : ‖Q x‖ ≤ 2*‖P‖*M^3 := by
  have h1 := norm_cubicForm_of_caps P (A1 x) (C1 x) (B1 x) M M M hM hM hM hAv1 hCv1 hBv1
  have h2 := norm_cubicForm_of_caps P (A2 x) (C2 x) (B2 x) M M M hM hM hM hAv2 hCv2 hBv2
  change ‖cubicForm P (A1 x) (C1 x) (B1 x)+cubicForm P (A2 x) (C2 x) (B2 x)‖ ≤ _
  calc
    _ ≤ ‖cubicForm P (A1 x) (C1 x) (B1 x)‖+‖cubicForm P (A2 x) (C2 x) (B2 x)‖ :=
      norm_add_le (cubicForm P (A1 x) (C1 x) (B1 x)) (cubicForm P (A2 x) (C2 x) (B2 x))
    _ ≤ ‖P‖*M*M*M+‖P‖*M*M*M := add_le_add h1 h2
    _ = 2*‖P‖*M^3 := by ring

private lemma norm_directional_pairedCubicForm_le (M M1 : ℝ) (hM : 0 ≤ M) (hM1 : 0 ≤ M1)
    (hAv1 : ‖A1 x‖ ≤ M) (hCv1 : ‖C1 x‖ ≤ M) (hAv2 : ‖A2 x‖ ≤ M) (hCv2 : ‖C2 x‖ ≤ M)
    (hBv1 : ‖B1 x‖ ≤ M) (hBv2 : ‖B2 x‖ ≤ M)
    (hAd1 : ‖fderiv ℝ A1 x‖ ≤ M1) (hCd1 : ‖fderiv ℝ C1 x‖ ≤ M1)
    (hAd2 : ‖fderiv ℝ A2 x‖ ≤ M1) (hCd2 : ‖fderiv ℝ C2 x‖ ≤ M1)
    (hBd1 : ‖fderiv ℝ B1 x‖ ≤ M1) (hBd2 : ‖fderiv ℝ B2 x‖ ≤ M1) :
    ‖directionalFDeriv X Q x‖ ≤ (6*‖P‖*M^2*M1)*‖X‖ := by
  have hDA1 : ‖directionalFDeriv X A1 x‖ ≤ M1*‖X‖ :=
    ((fderiv ℝ A1 x).le_opNorm X).trans
      (mul_le_mul_of_nonneg_right hAd1 (norm_nonneg X))
  have hDC1 : ‖directionalFDeriv X C1 x‖ ≤ M1*‖X‖ :=
    ((fderiv ℝ C1 x).le_opNorm X).trans
      (mul_le_mul_of_nonneg_right hCd1 (norm_nonneg X))
  have hDA2 : ‖directionalFDeriv X A2 x‖ ≤ M1*‖X‖ :=
    ((fderiv ℝ A2 x).le_opNorm X).trans
      (mul_le_mul_of_nonneg_right hAd2 (norm_nonneg X))
  have hDC2 : ‖directionalFDeriv X C2 x‖ ≤ M1*‖X‖ :=
    ((fderiv ℝ C2 x).le_opNorm X).trans
      (mul_le_mul_of_nonneg_right hCd2 (norm_nonneg X))
  have hDB1 : ‖directionalFDeriv X B1 x‖ ≤ M1*‖X‖ :=
    ((fderiv ℝ B1 x).le_opNorm X).trans
      (mul_le_mul_of_nonneg_right hBd1 (norm_nonneg X))
  have hDB2 : ‖directionalFDeriv X B2 x‖ ≤ M1*‖X‖ :=
    ((fderiv ℝ B2 x).le_opNorm X).trans
      (mul_le_mul_of_nonneg_right hBd2 (norm_nonneg X))
  have h1 := norm_cubicDerivative_le P (A1 x) (C1 x)
    (directionalFDeriv X A1 x) (directionalFDeriv X C1 x) (B1 x) (directionalFDeriv X B1 x)
    M (M1*‖X‖) hM (mul_nonneg hM1 (norm_nonneg X)) hAv1 hCv1 hBv1 hDA1 hDC1 hDB1
  have h2 := norm_cubicDerivative_le P (A2 x) (C2 x)
    (directionalFDeriv X A2 x) (directionalFDeriv X C2 x) (B2 x) (directionalFDeriv X B2 x)
    M (M1*‖X‖) hM (mul_nonneg hM1 (norm_nonneg X)) hAv2 hCv2 hBv2 hDA2 hDC2 hDB2
  rw [directional_pairedCubicForm P A1 C1 A2 C2 B1 B2 x X hA1 hC1 hA2 hC2 hB1 hB2]
  calc
    _ ≤ ‖cubicDerivative P (A1 x) (C1 x) (directionalFDeriv X A1 x)
        (directionalFDeriv X C1 x) (B1 x) (directionalFDeriv X B1 x)‖+
      ‖cubicDerivative P (A2 x) (C2 x) (directionalFDeriv X A2 x)
        (directionalFDeriv X C2 x) (B2 x) (directionalFDeriv X B2 x)‖ :=
      norm_add_le
        (cubicDerivative P (A1 x) (C1 x) (directionalFDeriv X A1 x)
          (directionalFDeriv X C1 x) (B1 x) (directionalFDeriv X B1 x))
        (cubicDerivative P (A2 x) (C2 x) (directionalFDeriv X A2 x)
          (directionalFDeriv X C2 x) (B2 x) (directionalFDeriv X B2 x))
    _ ≤ 3*‖P‖*M^2*(M1*‖X‖)+3*‖P‖*M^2*(M1*‖X‖) := add_le_add h1 h2
    _ = (6*‖P‖*M^2*M1)*‖X‖ := by ring

theorem norm_fderiv_pairedCubicForm_le (M M1 : ℝ) (hM : 0 ≤ M) (hM1 : 0 ≤ M1)
    (hAv1 : ‖A1 x‖ ≤ M) (hCv1 : ‖C1 x‖ ≤ M) (hAv2 : ‖A2 x‖ ≤ M) (hCv2 : ‖C2 x‖ ≤ M)
    (hBv1 : ‖B1 x‖ ≤ M) (hBv2 : ‖B2 x‖ ≤ M)
    (hAd1 : ‖fderiv ℝ A1 x‖ ≤ M1) (hCd1 : ‖fderiv ℝ C1 x‖ ≤ M1)
    (hAd2 : ‖fderiv ℝ A2 x‖ ≤ M1) (hCd2 : ‖fderiv ℝ C2 x‖ ≤ M1)
    (hBd1 : ‖fderiv ℝ B1 x‖ ≤ M1) (hBd2 : ‖fderiv ℝ B2 x‖ ≤ M1) :
    ‖(fderiv ℝ Q x : R3 →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)‖ ≤ 6*‖P‖*M^2*M1 := by
  refine fullCubicDerivative_opNorm_le_bound _ _ (by positivity) (fun X => ?_)
  exact norm_directional_pairedCubicForm_le P A1 C1 A2 C2 B1 B2 x X hA1 hC1 hA2 hC2 hB1 hB2
    M M1 hM hM1 hAv1 hCv1 hAv2 hCv2 hBv1 hBv2 hAd1 hCd1 hAd2 hCd2 hBd1 hBd2

theorem norm_fderiv_weightedPairedCubicForm_le (s : R3 → ℝ) (hs : DifferentiableAt ℝ s x)
    (M M1 : ℝ) (hM : 0 ≤ M) (hM1 : 0 ≤ M1)
    (hAv1 : ‖A1 x‖ ≤ M) (hCv1 : ‖C1 x‖ ≤ M) (hAv2 : ‖A2 x‖ ≤ M) (hCv2 : ‖C2 x‖ ≤ M)
    (hBv1 : ‖B1 x‖ ≤ M) (hBv2 : ‖B2 x‖ ≤ M)
    (hAd1 : ‖fderiv ℝ A1 x‖ ≤ M1) (hCd1 : ‖fderiv ℝ C1 x‖ ≤ M1)
    (hAd2 : ‖fderiv ℝ A2 x‖ ≤ M1) (hCd2 : ‖fderiv ℝ C2 x‖ ≤ M1)
    (hBd1 : ‖fderiv ℝ B1 x‖ ≤ M1) (hBd2 : ‖fderiv ℝ B2 x‖ ≤ M1) :
    ‖(fderiv ℝ (fun y : R3 => s y • Q y) x : R3 →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)‖ ≤
      ‖fderiv ℝ s x‖*(2*‖P‖*M^3)+|s x| *(6*‖P‖*M^2*M1) := by
  refine fullCubicDerivative_opNorm_le_bound _ _ (by positivity) (fun X => ?_)
  let Qval : E →L[ℝ] E →L[ℝ] ℝ := pairedCubicForm P (A1 x) (C1 x) (A2 x) (C2 x) (B1 x) (B2 x)
  let Dval : E →L[ℝ] E →L[ℝ] ℝ :=
    cubicDerivative P (A1 x) (C1 x) (directionalFDeriv X A1 x) (directionalFDeriv X C1 x)
      (B1 x) (directionalFDeriv X B1 x)+
    cubicDerivative P (A2 x) (C2 x) (directionalFDeriv X A2 x) (directionalFDeriv X C2 x)
      (B2 x) (directionalFDeriv X B2 x)
  let dscalar : ℝ := directionalFDeriv X s x
  have hV : ‖Qval‖ ≤ 2*‖P‖*M^3 :=
    norm_pairedCubicForm_le P A1 C1 A2 C2 B1 B2 x M hM hAv1 hCv1 hAv2 hCv2 hBv1 hBv2
  have hDdir := norm_directional_pairedCubicForm_le P A1 C1 A2 C2 B1 B2 x X hA1 hC1 hA2 hC2 hB1 hB2
    M M1 hM hM1 hAv1 hCv1 hAv2 hCv2 hBv1 hBv2 hAd1 hCd1 hAd2 hCd2 hBd1 hBd2
  have hD : ‖Dval‖ ≤ (6*‖P‖*M^2*M1)*‖X‖ := by
    have hDir := directional_pairedCubicForm P A1 C1 A2 C2 B1 B2 x X hA1 hC1 hA2 hC2 hB1 hB2
    change directionalFDeriv X Q x=Dval at hDir
    rw [hDir] at hDdir
    exact hDdir
  have hS : |dscalar| ≤ ‖fderiv ℝ s x‖*‖X‖ := by
    simpa only [dscalar,directionalFDeriv,Real.norm_eq_abs] using (fderiv ℝ s x).le_opNorm X
  have hScale1 : ‖dscalar • Qval‖=|dscalar| *‖Qval‖ := forms_norm_smul dscalar Qval
  have hScale2 : ‖s x • Dval‖=|s x| *‖Dval‖ := forms_norm_smul (s x) Dval
  change ‖directionalFDeriv X (fun y => s y • Q y) x‖ ≤ _
  rw [directional_weightedPairedCubicForm P A1 C1 A2 C2 B1 B2 x X hA1 hC1 hA2 hC2 hB1 hB2 s hs]
  change ‖dscalar • Qval+s x • Dval‖ ≤ _
  calc
    _ ≤ ‖dscalar • Qval‖+‖s x • Dval‖ := norm_add_le (dscalar • Qval) (s x • Dval)
    _ = |dscalar| *‖Qval‖+|s x| *‖Dval‖ := congrArg₂ (fun a b : ℝ => a+b) hScale1 hScale2
    _ ≤ (‖fderiv ℝ s x‖*‖X‖)*(2*‖P‖*M^3)+|s x| *((6*‖P‖*M^2*M1)*‖X‖) :=
      add_le_add (mul_le_mul hS hV (norm_nonneg Qval) (by positivity))
        (mul_le_mul_of_nonneg_left hD (abs_nonneg (s x)))
    _ = (‖fderiv ℝ s x‖*(2*‖P‖*M^3)+|s x| *(6*‖P‖*M^2*M1))*‖X‖ := by ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCubicProductDerivative
