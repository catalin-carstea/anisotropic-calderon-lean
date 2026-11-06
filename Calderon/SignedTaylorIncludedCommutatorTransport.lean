import Calderon.SignedTaylorOperatorIntertwining
import Calderon.SignedTaylorFixedBimoduleTransport

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError

lemma secondTaylorRemainder_included_commutator
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : ℝ → X →L[ℝ] X) (S : ℝ → X →L[ℝ] Y)
    (I : X →L[ℝ] Y) (M : X →L[ℝ] X) (N : Y →L[ℝ] Y) (r : ℝ)
    (hA : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ A (θ*r))
    (hS : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ S (θ*r))
    (hEq : ∀ θ ∈ Icc (0 : ℝ) 1,
      (fun τ => I.comp (A τ)) =ᶠ[𝓝 (θ*r)] (fun τ => (S τ).comp M-N.comp (S τ))) :
    I.comp (secondTaylorRemainder A r) =
      (secondTaylorRemainder S r).comp M-N.comp (secondTaylorRemainder S r) := by
  let Comm : ℝ → X →L[ℝ] Y := fun τ => (S τ).comp M-N.comp (S τ)
  have hComm (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ Comm (θ*r) :=
    ((hS θ hθ).clm_comp contDiffAt_const).sub (contDiffAt_const.clm_comp (hS θ hθ))
  have hGerm (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun τ => I.comp (A τ)) =ᶠ[𝓝 (θ*r)]
        (fun τ => (Comm τ).comp (ContinuousLinearMap.id ℝ X)) := by
    filter_upwards [hEq θ hθ] with τ hτ
    exact hτ.trans (ContinuousLinearMap.comp_id (Comm τ)).symm
  have hIntertwine := secondTaylorRemainder_operator_intertwining
    A Comm (ContinuousLinearMap.id ℝ X) I r hA hComm hGerm
  calc
    I.comp (secondTaylorRemainder A r) =
        (secondTaylorRemainder Comm r).comp (ContinuousLinearMap.id ℝ X) := hIntertwine
    _ = secondTaylorRemainder Comm r := ContinuousLinearMap.comp_id _
    _ = (secondTaylorRemainder S r).comp M-N.comp (secondTaylorRemainder S r) :=
      secondTaylorRemainder_fixed_commutator S M N r hS

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.secondTaylorRemainder_included_commutator
