import Calderon.ActualFiniteHarmonicModelSupportLocalEnergyIntegral

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  SectionFiveErrorForms ReferenceDensityBounds BaseDensityAdjoint PrincipalCommutator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev supportedScalarEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] supportedScalarEnergyFunction

lemma tsupport_coreDirectionalDerivative_subset (v : R3)
    (F : smoothCompactFiniteSphereCore hO hD) :
    tsupport (fun x => coreDirectionalDerivative hO hD v F x) ⊆ tsupport (F : R3 → SphereL2) := by
  exact tsupport_fderiv_apply_subset ℝ v

theorem nativeCore_supported_integral_energy_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (beta : R3 → ℝ) (hbeta : Continuous beta) (hpos : ∀ x, 0 < beta x)
    (A : ℝ) (hA : 0 ≤ A) (K : Set R3)
    (F : smoothCompactFiniteSphereCore hO hD) (f : R3 → ℝ)
    (hzero : ∀ x ∉ K, f x = 0)
    (hbound : ∀ x ∈ K, |f x| ≤ A*(referenceDensityFamily g L (lam,x)*
      finiteCoreSourceEnergy hO hD (beta x) F x)) :
    |∫ x : R3, f x| ≤ A * ∫ x : R3, referenceDensityFamily g L (lam,x)*
      finiteCoreSourceEnergy hO hD (beta x) F x := by
  have hglobal (x : R3) : |f x| ≤ A*(referenceDensityFamily g L (lam,x)*
      finiteCoreSourceEnergy hO hD (beta x) F x) := by
    by_cases hx : x ∈ K
    · exact hbound x hx
    · rw [hzero x hx,abs_zero]
      exact mul_nonneg hA (mul_nonneg (referenceDensityFamily_pos g hg L (lam,x)).le
        (finiteCoreSourceEnergy_nonneg hO hD (beta x) (hpos x).le F x))
  have hN : Integrable (fun x : R3 => referenceDensityFamily g L (lam,x)*
      finiteCoreSourceEnergy hO hD (beta x) F x) :=
    integrable_native_core_source_norm hO hD g hg L lam beta hbeta hpos F
  have hi := norm_integral_le_of_norm_le (f := f) (hN.const_mul A)
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hglobal x))
  rw [integral_const_mul] at hi
  simpa only [Real.norm_eq_abs] using hi

theorem nativeCore_density_test_energy_bound_of_support_local
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (beta : R3 → ℝ) (hbeta : Continuous beta) (hpos : ∀ x, 0 < beta x)
    (A : ℝ) (hA : 0 ≤ A) (K : Set R3)
    (U V F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport (V : R3 → SphereL2) ⊆ K)
    (hbound : ∀ x ∈ K, |⟪U x,V x⟫_ℝ| ≤ A*finiteCoreSourceEnergy hO hD (beta x) F x) :
    |∫ x : R3, referenceDensityFamily g L (lam,x)*⟪U x,V x⟫_ℝ| ≤
      A * ∫ x : R3, referenceDensityFamily g L (lam,x)*finiteCoreSourceEnergy hO hD (beta x) F x := by
  apply nativeCore_supported_integral_energy_bound hO hD g hg L lam beta hbeta hpos A hA K F
  · intro x hx
    have hz : V x = 0 := image_eq_zero_of_notMem_tsupport (fun hy => hx (hsupp hy))
    rw [hz,inner_zero_right,mul_zero]
  · intro x hx
    rw [abs_mul,abs_of_pos (referenceDensityFamily_pos g hg L (lam,x))]
    calc
      _ ≤ referenceDensityFamily g L (lam,x)*(A*finiteCoreSourceEnergy hO hD (beta x) F x) :=
        mul_le_mul_of_nonneg_left (hbound x hx) (referenceDensityFamily_pos g hg L (lam,x)).le
      _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
