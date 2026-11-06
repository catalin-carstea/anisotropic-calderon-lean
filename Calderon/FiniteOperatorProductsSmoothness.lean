import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma contDiffOn_fin_three_operator_products
    (X E F : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : Set X) (w : X → ℝ) (Q : Fin 3 → Fin 3 → X → ℝ)
    (Fh Fbh : Fin 3 → X → E →L[ℝ] E)
    (Fl Fbl : Fin 3 → X → F →L[ℝ] F)
    (WE Eb : Fin 3 → X → E →L[ℝ] F)
    (hw : ContDiffOn ℝ ∞ w U)
    (hQ : ∀ i j : Fin 3, ContDiffOn ℝ ∞ (Q i j) U)
    (hFh : ∀ i : Fin 3, ContDiffOn ℝ ∞ (Fh i) U)
    (hFbh : ∀ i : Fin 3, ContDiffOn ℝ ∞ (Fbh i) U)
    (hFl : ∀ i : Fin 3, ContDiffOn ℝ ∞ (Fl i) U)
    (hFbl : ∀ i : Fin 3, ContDiffOn ℝ ∞ (Fbl i) U)
    (hWE : ∀ i : Fin 3, ContDiffOn ℝ ∞ (WE i) U)
    (hEb : ∀ i : Fin 3, ContDiffOn ℝ ∞ (Eb i) U) :
    ContDiffOn ℝ ∞ (fun x : X => ∑ i : Fin 3, ∑ j : Fin 3,
      Q i j x • ((Fl i x).comp (WE j x)+(WE i x).comp (Fh j x))) U ∧
    ContDiffOn ℝ ∞ (fun x : X => w x •
      (∑ i : Fin 3, ∑ j : Fin 3,
        Q i j x • ((Eb j x).comp (Fbh i x)+(Fbl j x).comp (Eb i x)))) U := by
  constructor
  · exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      (hQ i j).smul
        (((hFl i).clm_comp (hWE j)).add ((hWE i).clm_comp (hFh j)))))
  · exact hw.smul (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      (hQ i j).smul
        (((hEb j).clm_comp (hFbh i)).add ((hFbl j).clm_comp (hEb i))))))


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_fin_three_operator_products
