import Calderon.ActualFiniteHarmonicModelSupportedScalarEnergyIntegral
import Calderon.NativeCoreCoefficientSecondIntegrationByParts

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  SectionFiveErrorForms ReferenceDensityBounds BaseDensityAdjoint PrincipalCommutator ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev secondBaseHalfEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] secondBaseHalfEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy

theorem nativeCore_second_base_half_form_energy_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (beta : R3 → ℝ) (hbeta : Continuous beta) (hpos : ∀ x, 0 < beta x)
    (A M : ℝ) (hA : 0 ≤ A) (hM : 0 ≤ M) (K : Set R3)
    (T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (i k : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport (F : R3 → SphereL2) ⊆ K)
    (hT : ∀ x ∈ K, ∀ U V : smoothCompactFiniteSphereCore hO hD,
      |⟪T U x,V x⟫_ℝ| ≤ (A/beta x)*
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖)
    (hDT : ∀ x ∈ K, ∀ U V : smoothCompactFiniteSphereCore hO hD,
      |⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i)) T U x,V x⟫_ℝ| ≤ A*
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖)
    (hmu : ∀ x ∈ K, |directionalFDeriv (coordinateDirection i)
      (fun y => referenceDensityFamily g L (lam,y)) x| ≤
      M*beta x*referenceDensityFamily g L (lam,x)) :
    |∫ x : R3, referenceDensityFamily g L (lam,x)*
      ⟪T (coreDirectionalDerivative hO hD (coordinateDirection i)
        (coreDirectionalDerivative hO hD (coordinateDirection k) F)) x,F x⟫_ℝ| ≤
      ((2+M)*A) * ∫ x : R3, referenceDensityFamily g L (lam,x)*
        finiteCoreSourceEnergy hO hD (beta x) F x := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  let di := coreDirectionalDerivative hO hD (coordinateDirection i)
  let dk := coreDirectionalDerivative hO hD (coordinateDirection k)
  let S := coefficientDerivative di T
  let J := ∫ x : R3, mu x*finiteCoreSourceEnergy hO hD (beta x) F x
  let P := ∫ x : R3, mu x*⟪T (dk F) x,di F x⟫_ℝ
  let Q := ∫ x : R3, mu x*⟪S (dk F) x,F x⟫_ℝ
  let R := ∫ x : R3, directionalFDeriv (coordinateDirection i) mu x*⟪T (dk F) x,F x⟫_ℝ
  have hP : |P| ≤ A*J := by
    apply nativeCore_density_test_energy_bound_of_support_local hO hD g hg L lam beta hbeta hpos A hA K
      (T (dk F)) (di F) F ((tsupport_coreDirectionalDerivative_subset hO hD _ F).trans hsupp)
    intro x hx
    calc
      _ ≤ (A/beta x)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (dk F) x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (di F) x‖ := hT x hx _ _
      _ = A*((beta x)⁻¹*(‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (dk F) x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (di F) x‖)) := by rw [div_eq_mul_inv]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (inv_beta_mul_gradient_norms_le_finiteCoreSourceEnergy hO hD (beta x) (hpos x).le F x k i) hA
  have hQ : |Q| ≤ A*J := by
    apply nativeCore_density_pair_energy_bound_of_support_local hO hD g hg L lam beta hbeta hpos A hA K
      (S (dk F)) F hsupp
    intro x hx
    calc
      _ ≤ A*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (dk F) x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ := hDT x hx _ _
      _ = A*(‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (dk F) x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (norm_half_mul_gradient_half_le_finiteCoreSourceEnergy hO hD (beta x) (hpos x) F x k) hA
  have hR : |R| ≤ (M*A)*J := by
    apply nativeCore_supported_integral_energy_bound hO hD g hg L lam beta hbeta hpos (M*A)
      (mul_nonneg hM hA) K F
    · intro x hx
      have hz : F x = 0 := image_eq_zero_of_notMem_tsupport (fun hy => hx (hsupp hy))
      rw [hz,inner_zero_right,mul_zero]
    · intro x hx
      let u := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (dk F) x‖
      let v := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖
      have hmpos : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (lam,x)).le
      have hc : (M*beta x*mu x)*((A/beta x)*u*v) = (M*A*mu x)*(v*u) := by
        field_simp [(hpos x).ne']
        <;> ring
      rw [abs_mul]
      calc
        _ ≤ (M*beta x*mu x)*((A/beta x)*u*v) := mul_le_mul (hmu x hx) (hT x hx _ _)
          (abs_nonneg _) (mul_nonneg (mul_nonneg hM (hpos x).le) hmpos)
        _ = (M*A*mu x)*(v*u) := hc
        _ ≤ (M*A*mu x)*finiteCoreSourceEnergy hO hD (beta x) F x :=
          mul_le_mul_of_nonneg_left
            (norm_half_mul_gradient_half_le_finiteCoreSourceEnergy hO hD (beta x) (hpos x) F x k)
            (mul_nonneg (mul_nonneg hM hA) hmpos)
        _ = _ := by ring
  have he := native_core_coefficient_second_integration_by_parts hO hD g hg L lam T i k F F
  change (∫ x : R3, mu x*⟪T (di (dk F)) x,F x⟫_ℝ) = -P-Q-R at he
  rw [he]
  calc
    _ ≤ |P|+|Q|+|R| := by
      calc
        _ ≤ |-P-Q|+|R| := abs_sub _ _
        _ ≤ (|-P|+|Q|)+|R| := add_le_add (abs_sub _ _) le_rfl
        _ = _ := by rw [abs_neg]
    _ ≤ A*J+A*J+(M*A)*J := add_le_add (add_le_add hP hQ) hR
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
