import Calderon.ActualFiniteHarmonicModelSupportLocalEnergyIntegral

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  SectionFiveErrorForms ReferenceDensityBounds BaseDensityAdjoint PrincipalCommutator ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev firstBaseHalfEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] firstBaseHalfEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy

theorem nativeCore_first_base_half_form_energy_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (beta : R3 → ℝ) (hbeta : Continuous beta) (hpos : ∀ x, 0 < beta x)
    (A : ℝ) (hA : 0 ≤ A) (K : Set R3)
    (T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport (F : R3 → SphereL2) ⊆ K)
    (hT : ∀ x ∈ K, ∀ U V : smoothCompactFiniteSphereCore hO hD,
      |⟪T U x,V x⟫_ℝ| ≤ A*
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖) :
    |∫ x : R3, referenceDensityFamily g L (lam,x)*
      ⟪T (coreDirectionalDerivative hO hD (coordinateDirection j) F) x,F x⟫_ℝ| ≤
      A * ∫ x : R3, referenceDensityFamily g L (lam,x)*
        finiteCoreSourceEnergy hO hD (beta x) F x := by
  apply nativeCore_density_pair_energy_bound_of_support_local hO hD g hg L lam beta hbeta hpos A hA K
    (T (coreDirectionalDerivative hO hD (coordinateDirection j) F)) F hsupp
  intro x hx
  calc
    _ ≤ A*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ := hT x hx _ _
    _ = A*(‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
          (coreDirectionalDerivative hO hD (coordinateDirection j) F) x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (norm_half_mul_gradient_half_le_finiteCoreSourceEnergy hO hD (beta x) (hpos x) F x j) hA

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
