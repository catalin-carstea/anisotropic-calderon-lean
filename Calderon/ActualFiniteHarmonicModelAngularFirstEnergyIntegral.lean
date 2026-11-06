import Calderon.ActualFiniteHarmonicModelAngularSecondEnergyIntegral

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  SectionFiveErrorForms ReferenceDensityBounds BaseDensityAdjoint
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularFirstEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularFirstEnergyFunction

lemma angular_first_scalar_le_sourceEnergy
    (hF : SphereFischerInner) (a j : Fin 3) (beta C eps c : ℝ)
    (hb : 0 < beta) (hC : 0 ≤ C) (heps : 0 ≤ eps) (hc : |c| ≤ C*eps)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |c * ⟪coreDerivative hO hD hF a
      (coreDirectionalDerivative hO hD (coordinateDirection j) F) x,F x⟫_ℝ| ≤
      (4*C*eps)*finiteCoreSourceEnergy hO hD beta F x := by
  rw [abs_mul]
  have hp := abs_inner_coreDerivative_le_half hO hD hF a
    (coreDirectionalDerivative hO hD (coordinateDirection j) F) F x
  have he := norm_half_mul_gradient_half_le_finiteCoreSourceEnergy hO hD beta hb F x j
  calc
    _ ≤ (C*eps)*(4*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
      (coreDirectionalDerivative hO hD (coordinateDirection j) F) x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖) :=
      mul_le_mul hc hp (abs_nonneg _) (by positivity)
    _ = (4*C*eps)*(‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

theorem coreDerivative_firstBase_scalar_integral_bound
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (a j : Fin 3) (C eps : ℝ) (hC : 0 ≤ C) (heps : 0 ≤ eps)
    (beta : R3 → ℝ) (hbeta : Continuous beta) (hpos : ∀ x, 0 < beta x)
    (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (K : Set R3)
    (hc0 : ∀ x ∈ K, |c x| ≤ C*eps)
    (F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport (F : R3 → SphereL2) ⊆ K) :
    |∫ x : R3, referenceDensityFamily g L (lam,x) * c x *
      ⟪coreDerivative hO hD hF a
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x,F x⟫_ℝ| ≤
      (4*C*eps) * ∫ x : R3, referenceDensityFamily g L (lam,x) *
        finiteCoreSourceEnergy hO hD (beta x) F x := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  let U := coreDerivative hO hD hF a (coreDirectionalDerivative hO hD (coordinateDirection j) F)
  have hbound (x : R3) : |mu x*c x*⟪U x,F x⟫_ℝ| ≤
      (4*C*eps)*(mu x*finiteCoreSourceEnergy hO hD (beta x) F x) := by
    have hm0 : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (lam,x)).le
    by_cases hx : x ∈ K
    · have hp := angular_first_scalar_le_sourceEnergy hO hD hF a j
        (beta x) C eps (c x) (hpos x) hC heps (hc0 x hx) F x
      calc
        _ = mu x * |c x*⟪U x,F x⟫_ℝ| := by rw [mul_assoc,abs_mul,abs_of_nonneg hm0]
        _ ≤ mu x * ((4*C*eps)*finiteCoreSourceEnergy hO hD (beta x) F x) :=
          mul_le_mul_of_nonneg_left hp hm0
        _ = _ := by ring
    · have hzF : F x = 0 := image_eq_zero_of_notMem_tsupport (fun hy => hx (hsupp hy))
      have hN := finiteCoreSourceEnergy_nonneg hO hD (beta x) (hpos x).le F x
      simp only [hzF,inner_zero_right,mul_zero,abs_zero]
      positivity
  have hN : Integrable (fun x : R3 => mu x*finiteCoreSourceEnergy hO hD (beta x) F x) :=
    integrable_native_core_source_norm hO hD g hg L lam beta hbeta hpos F
  have hi := norm_integral_le_of_norm_le (f := fun x : R3 => mu x*c x*⟪U x,F x⟫_ℝ)
    (hN.const_mul (4*C*eps))
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound x))
  rw [integral_const_mul] at hi
  simpa only [Real.norm_eq_abs,mu,U] using hi

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
