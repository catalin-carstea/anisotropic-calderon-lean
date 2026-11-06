import Calderon.SignedTaylorIncludedCommutatorTransport
import Calderon.SphereSobolevInclusion
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open ConnectionError SphereHarmonic
attribute [local irreducible] secondTaylorRemainder
lemma secondTaylorRemainder_included_commutator_sphere
    (A : ℝ → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
    (S : ℝ → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (M : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
    (N : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) (r : ℝ)
    (hA : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ A (θ*r))
    (hS : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ S (θ*r))
    (hEq : ∀ θ ∈ Icc (0 : ℝ) 1,
      (fun τ => I.comp (A τ)) =ᶠ[𝓝 (θ*r)] (fun τ => (S τ).comp M-N.comp (S τ))) :
    I.comp (secondTaylorRemainder A r) =
      (secondTaylorRemainder S r).comp M-N.comp (secondTaylorRemainder S r) :=
  secondTaylorRemainder_included_commutator A S I M N r hA hS hEq

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
