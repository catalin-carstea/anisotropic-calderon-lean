import Calderon.ActualFiniteHarmonicModelSupportLocalEnergyIntegral

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  SectionFiveErrorForms ReferenceDensityBounds BaseDensityAdjoint
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev densityPairLinearFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] densityPairLinearFunction

def nativeCoreDensityPairLinearMap
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (G : smoothCompactFiniteSphereCore hO hD) :
    smoothCompactFiniteSphereCore hO hD →ₗ[ℝ] ℝ where
  toFun U := ∫ x : R3, referenceDensityFamily g L (lam,x)*⟪U x,G x⟫_ℝ
  map_add' U V := by
    simp only [Submodule.coe_add,Pi.add_apply,inner_add_left,mul_add]
    exact integral_add (integrable_native_core_density_pair hO hD g hg L lam U G)
      (integrable_native_core_density_pair hO hD g hg L lam V G)
  map_smul' c U := by
    change (∫ x : R3, referenceDensityFamily g L (lam,x)*⟪(c • U) x,G x⟫_ℝ) =
      c*(∫ x : R3, referenceDensityFamily g L (lam,x)*⟪U x,G x⟫_ℝ)
    calc
      _ = ∫ x : R3, c*(referenceDensityFamily g L (lam,x)*⟪U x,G x⟫_ℝ) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [Submodule.coe_smul,Pi.smul_apply,real_inner_smul_left]
        ring
      _ = _ := integral_const_mul _ _

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
