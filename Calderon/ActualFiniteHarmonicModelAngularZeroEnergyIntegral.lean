import Calderon.ActualFiniteHarmonicModelAngularFirstEnergyIntegral

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  SectionFiveErrorForms ReferenceDensityBounds BaseDensityAdjoint
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularZeroEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularZeroEnergyFunction

lemma beta_mul_half_norm_sq_le_finiteCoreSourceEnergy
    (beta : ℝ) (hb : 0 ≤ beta) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    beta * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖^2 ≤
      finiteCoreSourceEnergy hO hD beta F x := by
  let H (k : Fin 3) := coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
    (coreDirectionalDerivative hO hD (coordinateDirection k) F) x
  let V := coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x
  have hh := norm_bessel_half_le_threehalf hO hD (F x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x) V
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
    (coreWeightOperator_graph hO hD (besselWeight (3/2 : ℝ)) F x)
  have he : beta⁻¹*(∑ k, ‖H k‖^2)+beta*‖V‖^2 ≤
      finiteCoreSourceEnergy hO hD beta F x :=
    angular_error_terms_le_sourceNormSquareIntegrand beta _ _ _ _
  have hn : 0 ≤ beta⁻¹*(∑ k, ‖H k‖^2) :=
    mul_nonneg (inv_nonneg.mpr hb) (Finset.sum_nonneg (fun k _ => sq_nonneg ‖H k‖))
  calc
    _ ≤ beta*‖V‖^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) hb
    _ ≤ _ := by linarith

lemma angular_zero_scalar_le_sourceEnergy
    (hF : SphereFischerInner) (a : Fin 3) (beta C eps c : ℝ)
    (hb : 0 < beta) (hC : 0 ≤ C) (heps : 0 ≤ eps) (hc : |c| ≤ C*eps*beta)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |c * ⟪coreDerivative hO hD hF a F x,F x⟫_ℝ| ≤
      (4*C*eps)*finiteCoreSourceEnergy hO hD beta F x := by
  rw [abs_mul]
  have hp := abs_inner_coreDerivative_le_half hO hD hF a F F x
  have he := beta_mul_half_norm_sq_le_finiteCoreSourceEnergy hO hD beta hb.le F x
  calc
    _ ≤ (C*eps*beta)*(4*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖) :=
      mul_le_mul hc hp (abs_nonneg _) (by positivity)
    _ = (4*C*eps)*(beta*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

theorem coreDerivative_zeroBase_scalar_integral_bound
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (a : Fin 3) (C eps : ℝ) (hC : 0 ≤ C) (heps : 0 ≤ eps)
    (beta : R3 → ℝ) (hbeta : Continuous beta) (hpos : ∀ x, 0 < beta x)
    (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (K : Set R3)
    (hc0 : ∀ x ∈ K, |c x| ≤ C*eps*beta x)
    (F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport (F : R3 → SphereL2) ⊆ K) :
    |∫ x : R3, referenceDensityFamily g L (lam,x) * c x *
      ⟪coreDerivative hO hD hF a F x,F x⟫_ℝ| ≤
      (4*C*eps) * ∫ x : R3, referenceDensityFamily g L (lam,x) *
        finiteCoreSourceEnergy hO hD (beta x) F x := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  let U := coreDerivative hO hD hF a F
  have hbound (x : R3) : |mu x*c x*⟪U x,F x⟫_ℝ| ≤
      (4*C*eps)*(mu x*finiteCoreSourceEnergy hO hD (beta x) F x) := by
    have hm0 : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (lam,x)).le
    by_cases hx : x ∈ K
    · have hp := angular_zero_scalar_le_sourceEnergy hO hD hF a
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
