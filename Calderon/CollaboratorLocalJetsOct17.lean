import Calderon.CollaboratorSmoothRepOct17
import Calderon.FixedDirichletRegularity
import Calderon.FixedSobolevCalculus
import Calderon.CollaboratorUniqueContinuationDefinitionOct17
import Calderon.CollaboratorLocalJetsKeyOct17

/-! Local solutions of `div(A ∇u) = 0` with prescribed compatible 2-jet at a point
(Lassas–Liimatainen–Salo, Prop. A.5, Steps 1–3; helper for task 07). -/

noncomputable section
open MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity

/-- The 2-jet compatibility functional: `div(A ∇u)(p)` in terms of the jet `(ξ, H)` of `u`. -/
def jetFunctional (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (p : R3) (ξ : R3 →L[ℝ] ℝ)
    (H : R3 →L[ℝ] (R3 →L[ℝ] ℝ)) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (fderiv ℝ (fun z : R3 => A z i j) p (EuclideanSpace.single i 1) *
      ξ (EuclideanSpace.single j 1) +
    A p i j * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))

/-- Near every point there are local solutions with every compatible 2-jet. -/
theorem exists_local_solution_jet {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    (hpos : ∀ x, (A x).PosDef) (p : R3) :
    ∃ ρ > 0, ∀ (a : ℝ) (ξ : R3 →L[ℝ] ℝ) (H : R3 →L[ℝ] (R3 →L[ℝ] ℝ)),
      (∀ v w : R3, H v w = H w v) → jetFunctional A p ξ H = 0 →
      ∃ u : R3 → ℝ, ContDiffOn ℝ ∞ u (ball p ρ) ∧ (∀ x ∈ ball p ρ, divCoeffGrad A u x = 0) ∧
        u p = a ∧ fderiv ℝ u p = ξ ∧ fderiv ℝ (fderiv ℝ u) p = H := by
  obtain ⟨ρ, hρ, hle⟩ := Jets.exists_radius_compatSub_le_solSub hA hpos p
  refine ⟨ρ, hρ, fun a ξ H hH hJ => ?_⟩
  have hc : ((a, ξ, H) : Jets.J) ∈ Jets.compatSub A p :=
    Jets.mem_compatSub.mpr ⟨hH, by rw [Jets.Γ_apply_self]; exact hJ⟩
  obtain ⟨u, hu, hue, hj⟩ := Jets.mem_solSub.mp (hle hc)
  exact ⟨u, hu, hue, congrArg Prod.fst hj, congrArg (fun j : Jets.J => j.2.1) hj,
    congrArg (fun j : Jets.J => j.2.2) hj⟩

end OAI.AnisotropicCalderon.Regularity
