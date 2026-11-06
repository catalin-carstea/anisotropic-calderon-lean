import Calderon.FixedDirichletRegularity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Weak unique continuation

Classical weak unique continuation for second-order elliptic equations in divergence form with
smooth symmetric positive definite coefficients (Aronszajn 1957; Hörmander's Carleman estimates;
e.g. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Thm 17.2.6):
a smooth solution of `div(A ∇u) = 0` on a connected open set that vanishes on a nonempty open
subset vanishes identically.

This module states the proposition and its divergence-form operator. The theorems that use it
take an explicit hypothesis `hUCP : UniqueContinuation`; the proposition is proved as
`uniqueContinuation` in `Calderon.CollaboratorUniqueContinuationProofOct17`. -/

noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon

/-- The divergence-form operator `div(A ∇u)` at `x`, in coordinates. -/
def divCoeffGrad (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (u : R3 → ℝ) (x : R3) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun z : R3 => ∑ j : Fin 3, A z i j *
    fderiv ℝ u z (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)

/-- **Weak unique continuation** for `div(A ∇u) = 0` with smooth, symmetric positive definite
`A` on a connected open set `Ω ⊆ ℝ³`. -/
def UniqueContinuation : Prop :=
  ∀ (Ω : Set R3), IsOpen Ω → IsConnected Ω →
    ∀ (A : R3 → Matrix (Fin 3) (Fin 3) ℝ), ContDiffOn ℝ ∞ A Ω → (∀ x ∈ Ω, (A x).PosDef) →
    ∀ (u : R3 → ℝ), ContDiffOn ℝ ∞ u Ω → (∀ x ∈ Ω, divCoeffGrad A u x = 0) →
    ∀ V : Set R3, IsOpen V → V.Nonempty → V ⊆ Ω → (∀ x ∈ V, u x = 0) →
    ∀ x ∈ Ω, u x = 0


end OAI.AnisotropicCalderon
