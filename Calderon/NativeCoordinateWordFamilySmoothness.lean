import Calderon.NativeCoordinateExpansionSmoothness
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon
open EnergyBridge DirichletFamily

lemma contDiffOn_wordFamily_of_hasFDerivAt_coordinateExpansion
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : List (Fin 3) → R3 → V) (Z : Set R3) (hZ : IsOpen Z)
    (hDerivative : ∀ (w : List (Fin 3)) (z : R3), z ∈ Z →
      HasFDerivAt (F w) (coordinateExpansion (fun i : Fin 3 => F (i::w) z)) z) :
    ∀ w : List (Fin 3), ContDiffOn ℝ (∞ : ℕ∞ω) (F w) Z := by
  have hFinite : ∀ n : ℕ, ∀ w : List (Fin 3),
      ContDiffOn ℝ (n : ℕ∞ω) (F w) Z := by
    intro n
    induction n with
    | zero =>
      intro w
      apply contDiffOn_zero.2
      intro z hz
      exact (hDerivative w z hz).continuousAt.continuousWithinAt
    | succ n ih =>
      intro w
      have hA : ContDiffOn ℝ (n : ℕ∞ω)
          (fun z => coordinateExpansion (fun i : Fin 3 => F (i::w) z)) Z :=
        contDiffOn_coordinateExpansion (n := (n : ℕ∞ω))
          Z (fun i z => F (i::w) z) (fun i => ih (i::w))
      have hSucc : ContDiffOn ℝ ((n : ℕ∞ω)+1) (F w) Z := by
        apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
          (n := (n : ℕ∞ω)) hZ.uniqueDiffOn).2
        refine ⟨by simp, fun z => coordinateExpansion (fun i : Fin 3 => F (i::w) z), hA, ?_⟩
        intro z hz
        exact (hDerivative w z hz).hasFDerivWithinAt
      simpa only [Nat.cast_add,Nat.cast_one] using hSucc
  intro w
  exact contDiffOn_infty.2 (fun n => hFinite n w)

end OAI.AnisotropicCalderon
#print axioms OAI.AnisotropicCalderon.contDiffOn_wordFamily_of_hasFDerivAt_coordinateExpansion
