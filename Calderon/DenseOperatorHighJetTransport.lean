import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DenseOperatorJetTransport
/-! Derive differentiated operator high graph from original undifferentiated identity.
Actual parents must discharge the seams. -/
lemma iteratedFDeriv_operator_high_graph
    {X E G V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Ω : Set X) (hΩ : IsOpen Ω) (p : X) (hp : p ∈ Ω)
    (I : E →L[ℝ] G) (S : X → (G →L[ℝ] V)) (T : X → (E →L[ℝ] V))
    (hS : ContDiffAt ℝ ∞ S p) (hT : ContDiffAt ℝ ∞ T p)
    (hIdentity : ∀ q ∈ Ω, (S q).comp I = T q)
    (k : ℕ) (d : Fin k → X) :
    (iteratedFDeriv ℝ k S p d).comp I = iteratedFDeriv ℝ k T p d := by
  let PreI : (G →L[ℝ] V) →L[ℝ] (E →L[ℝ] V) :=
    (ContinuousLinearMap.compL ℝ E G V).flip I
  have hLocal : (PreI ∘ S) =ᶠ[𝓝 p] T := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    exact hIdentity q hq
  have hDerivative := (hLocal.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds
  have hk : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by simp
  have hLeft := PreI.iteratedFDeriv_comp_left hS hk
  have hValue := congrArg (fun A => A d) hDerivative
  rw [hLeft] at hValue
  exact hValue
#print axioms OAI.AnisotropicCalderon.DenseOperatorJetTransport.iteratedFDeriv_operator_high_graph
end OAI.AnisotropicCalderon.DenseOperatorJetTransport
