import Calderon.ActualFiniteHarmonicModelAngularSecondEnergyPointwise
import Calderon.ActualFiniteHarmonicModelAngularSecondScalarOneParts
import Calderon.NativeCoreSourceNormIntegrability
import Calderon.ActualSupportLocalSecondForm

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  SectionFiveErrorForms ReferenceDensityBounds BaseDensityAdjoint
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeAngularEnergyIntegralFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeAngularEnergyIntegralFunction

theorem coreDerivative_secondBase_scalar_integral_bound
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (a i j : Fin 3) (C eps : ℝ) (hC : 0 ≤ C) (heps : 0 ≤ eps)
    (beta : R3 → ℝ) (hbeta : Continuous beta) (hpos : ∀ x, 0 < beta x)
    (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (K : Set R3)
    (hc0 : ∀ x ∈ K, |referenceDensityFamily g L (lam,x) * c x| ≤
      referenceDensityFamily g L (lam,x) * (C*eps/beta x))
    (hc1 : ∀ x ∈ K, |directionalDeriv (coordinateDirection i)
      (fun y => referenceDensityFamily g L (lam,y) * c y) x| ≤
      referenceDensityFamily g L (lam,x) * (C*eps))
    (F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport (F : R3 → SphereL2) ⊆ K) :
    |∫ x : R3, referenceDensityFamily g L (lam,x) * c x *
      ⟪coreDerivative hO hD hF a
        (coreDirectionalDerivative hO hD (coordinateDirection i)
          (coreDirectionalDerivative hO hD (coordinateDirection j) F)) x,F x⟫_ℝ| ≤
      (8*C*eps) * ∫ x : R3, referenceDensityFamily g L (lam,x) *
        finiteCoreSourceEnergy hO hD (beta x) F x := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  let U := coreDerivative hO hD hF a (coreDirectionalDerivative hO hD (coordinateDirection j) F)
  let V := coreDirectionalDerivative hO hD (coordinateDirection i) F
  let s : R3 → ℝ := directionalDeriv (coordinateDirection i) (fun y => mu y*c y)
  let t : R3 → ℝ := fun y => mu y*c y
  let A : R3 → ℝ := fun x => s x * ⟪F x,U x⟫_ℝ
  let B : R3 → ℝ := fun x => t x * ⟪V x,U x⟫_ℝ
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hs : ContDiff ℝ ∞ s := contDiff_directionalDeriv (coordinateDirection i) _ (hm.mul hc)
  have ht : ContDiff ℝ ∞ t := hm.mul hc
  have hA : Integrable A := by
    have hh := compact_inner_integrable (fun x => s x • F x) (U : R3 → SphereL2)
      (hs.smul F.property.1).continuous U.property.1.continuous U.property.2.1
    simpa only [real_inner_smul_left,A] using hh
  have hB : Integrable B := by
    have hh := compact_inner_integrable (fun x => t x • V x) (U : R3 → SphereL2)
      (ht.smul V.property.1).continuous U.property.1.continuous U.property.2.1
    simpa only [real_inner_smul_left,B] using hh
  have hparts := coreDerivative_secondBase_scalar_one_parts hO hD hF a
    (coordinateDirection i) (coordinateDirection j) mu c hm hc F F
  have hcombined : (∫ x : R3, mu x*c x *
      ⟪coreDerivative hO hD hF a
        (coreDirectionalDerivative hO hD (coordinateDirection i)
          (coreDirectionalDerivative hO hD (coordinateDirection j) F)) x,F x⟫_ℝ) =
      -(∫ x : R3, A x+B x) := by
    rw [integral_add hA hB]
    change (∫ x : R3, mu x*c x *
      ⟪coreDerivative hO hD hF a
        (coreDirectionalDerivative hO hD (coordinateDirection i)
          (coreDirectionalDerivative hO hD (coordinateDirection j) F)) x,F x⟫_ℝ) =
      -(∫ x : R3, A x) - (∫ x : R3, B x) at hparts
    linarith
  have hbound (x : R3) : |A x+B x| ≤
      (8*C*eps)*(mu x*finiteCoreSourceEnergy hO hD (beta x) F x) := by
    have hm0 : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (lam,x)).le
    by_cases hx : x ∈ K
    · have hp := angular_second_scalar_remainders_le_sourceEnergy hO hD hF a i j
        (beta x) (mu x) C eps (s x) (t x) (hpos x) hm0 hC heps
        (hc1 x hx) (hc0 x hx) F x
      calc
        _ ≤ |A x|+|B x| := abs_add_le _ _
        _ ≤ mu x*(8*C*eps)*finiteCoreSourceEnergy hO hD (beta x) F x := hp
        _ = _ := by ring
    · have hzF : F x = 0 := image_eq_zero_of_notMem_tsupport (fun hy => hx (hsupp hy))
      have hzV : V x = 0 := by
        change directionalDeriv (coordinateDirection i) (F : R3 → SphereL2) x = 0
        exact ActualSupportLocalSecondForm.directionalDeriv_eq_zero_off_support
          (F : R3 → SphereL2) K hsupp (coordinateDirection i) x hx
      have hN := finiteCoreSourceEnergy_nonneg hO hD (beta x) (hpos x).le F x
      simp only [A,B,hzF,hzV,inner_zero_left,mul_zero,add_zero,abs_zero]
      positivity
  have hN : Integrable (fun x : R3 => mu x*finiteCoreSourceEnergy hO hD (beta x) F x) :=
    integrable_native_core_source_norm hO hD g hg L lam beta hbeta hpos F
  have hi := norm_integral_le_of_norm_le (f := fun x : R3 => A x+B x)
    (hN.const_mul (8*C*eps))
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound x))
  rw [integral_const_mul] at hi
  rw [hcombined,abs_neg]
  simpa only [Real.norm_eq_abs,mu] using hi

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
