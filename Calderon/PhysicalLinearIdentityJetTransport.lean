import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.RotationCasimirJetTransport

/-! Differentiation of local scalar linear identities; the differentiated adjunction
and Casimir identities are conclusions. -/

lemma iteratedFDeriv_linear_scalar_identity
    {E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Ω : Set E) (hΩ : IsOpen Ω) (p : E) (hp : p ∈ Ω)
    (F : E → A) (G : E → B) (L : A →L[ℝ] ℝ) (R : B →L[ℝ] ℝ)
    (hF : ContDiffAt ℝ ∞ F p) (hG : ContDiffAt ℝ ∞ G p)
    (hIdentity : ∀ q ∈ Ω, L (F q) = R (G q))
    (j : ℕ) (d : Fin j → E) :
    L (iteratedFDeriv ℝ j F p d) = R (iteratedFDeriv ℝ j G p d) := by
  have hLocal : (L ∘ F) =ᶠ[𝓝 p] (R ∘ G) := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    exact hIdentity q hq
  have hDerivative := (hLocal.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds
  have hj : (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by simp
  have hLeft := L.iteratedFDeriv_comp_left hF hj
  have hRight := R.iteratedFDeriv_comp_left hG hj
  have hValue := congrArg (fun T => T d) hDerivative
  rw [hLeft, hRight] at hValue
  exact hValue

#print axioms OAI.AnisotropicCalderon.RotationCasimirJetTransport.iteratedFDeriv_linear_scalar_identity
end OAI.AnisotropicCalderon.RotationCasimirJetTransport
