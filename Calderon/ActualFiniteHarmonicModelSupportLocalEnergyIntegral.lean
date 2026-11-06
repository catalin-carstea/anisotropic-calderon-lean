import Calderon.ActualFiniteHarmonicModelSourceEnergyMixedProducts

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  SectionFiveErrorForms ReferenceDensityBounds BaseDensityAdjoint
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev coreLocalEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] coreLocalEnergyFunction

theorem nativeCore_density_pair_energy_bound_of_support_local
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (beta : R3 → ℝ) (hbeta : Continuous beta) (hpos : ∀ x, 0 < beta x)
    (A : ℝ) (hA : 0 ≤ A) (K : Set R3)
    (U F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport (F : R3 → SphereL2) ⊆ K)
    (hbound : ∀ x ∈ K, |⟪U x,F x⟫_ℝ| ≤ A*finiteCoreSourceEnergy hO hD (beta x) F x) :
    |∫ x : R3, referenceDensityFamily g L (lam,x)*⟪U x,F x⟫_ℝ| ≤
      A * ∫ x : R3, referenceDensityFamily g L (lam,x)*finiteCoreSourceEnergy hO hD (beta x) F x := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  have hglobal (x : R3) : |mu x*⟪U x,F x⟫_ℝ| ≤
      A*(mu x*finiteCoreSourceEnergy hO hD (beta x) F x) := by
    have hm : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (lam,x)).le
    have ht : |⟪U x,F x⟫_ℝ| ≤ A*finiteCoreSourceEnergy hO hD (beta x) F x := by
      by_cases hx : x ∈ K
      · exact hbound x hx
      · have hzF : F x = 0 := image_eq_zero_of_notMem_tsupport (fun hy => hx (hsupp hy))
        rw [hzF,inner_zero_right,abs_zero]
        exact mul_nonneg hA (finiteCoreSourceEnergy_nonneg hO hD (beta x) (hpos x).le F x)
    rw [abs_mul,abs_of_nonneg hm]
    calc
      _ ≤ mu x*(A*finiteCoreSourceEnergy hO hD (beta x) F x) := mul_le_mul_of_nonneg_left ht hm
      _ = _ := by ring
  have hN : Integrable (fun x : R3 => mu x*finiteCoreSourceEnergy hO hD (beta x) F x) :=
    integrable_native_core_source_norm hO hD g hg L lam beta hbeta hpos F
  have hpair := integrable_native_core_density_pair hO hD g hg L lam U F
  have hi := norm_integral_le_of_norm_le (f := fun x : R3 => mu x*⟪U x,F x⟫_ℝ)
    (hN.const_mul A)
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hglobal x))
  rw [integral_const_mul] at hi
  simpa only [Real.norm_eq_abs,mu] using hi

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
