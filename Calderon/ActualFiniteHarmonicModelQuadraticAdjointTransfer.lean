import Calderon.ActualFiniteHarmonicModelQuadraticAngularAdjoint
import Calderon.ActualFiniteHarmonicModelPointwiseAngularAdjoints

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SpectralCoreRegularity
  ActualReferenceDDSpectralTransport
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev quadraticTransferFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] quadraticTransferFunction

lemma hasCoreScalarExpansionBound_pointwise_adjoint
    (hF : SphereFischerInner) (A S : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hadj : ∀ F G : smoothCompactFiniteSphereCore hO hD, ∀ y : R3,
      ⟪A F y,G y⟫_ℝ=⟪F y,S G y⟫_ℝ)
    (x : R3) (C : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2) A x C) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2) S x C := by
  obtain ⟨T,ht,he⟩ := exists_pointwise_adjoint_of_quadratic_expansion hO hD hF A x C hA
  have hST : S=T := by
    apply coreEnd_eq_of_pointwise_inner_eq hO hD
    intro F G y
    calc
      ⟪S F y,G y⟫_ℝ = ⟪G y,S F y⟫_ℝ := real_inner_comm _ _
      _ = ⟪A G y,F y⟫_ℝ := (hadj G F y).symm
      _ = ⟪G y,T F y⟫_ℝ := ht G F y
      _ = ⟪T F y,G y⟫_ℝ := real_inner_comm _ _
  rwa [hST]

lemma inner_preserving_weight_adjoint
    (M : SphereL2 →L[ℝ] SphereL2) (hM : PreservesSphereSpectralGraphs hO hD M)
    (s : ℝ) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪M (coreWeightOperator hO hD (besselWeight s) F x),G x⟫_ℝ =
      ⟪F x,M.adjoint (coreWeightOperator hO hD (besselWeight s) G x)⟫_ℝ := by
  rw [← M.adjoint_inner_right]
  exact spectralGraph_inner_symm hO hD (besselWeight s)
    (F x) (coreWeightOperator hO hD (besselWeight s) F x)
    (M.adjoint (G x)) (M.adjoint (coreWeightOperator hO hD (besselWeight s) G x))
    (coreWeightOperator_graph hO hD (besselWeight s) F x)
    (preservesSphereSpectralGraphs_adjoint hO hD M hM _ _ _
      (coreWeightOperator_graph hO hD (besselWeight s) G x))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
