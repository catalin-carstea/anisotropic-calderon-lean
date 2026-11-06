import Calderon.ActualJacobiCompactExtensionRoom
import Calderon.NativeFiveHalfCoefficientMultiplierTopology

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ReferenceJacobiCompactExtensionRoom
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeFiveHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
variable {F : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 3}
  {K : Set (ℝ × (R3 × ℝ))}

attribute [local irreducible] nativeFiveHalfCoefficientMulL nativeThreeHalfCoefficientMulL

def jets4 (E : ReferenceJacobiCompactExtensionRoom F K) (i j : Fin 3)
    (p : ℝ × (R3 × ℝ)) : SmoothCoefficientJets 4 :=
  commonSupportCoefficientFamily 4 (E.scalar i j) (E.smooth i j) (E.spatialSupport i j)
    (E.spatialSupport_isCompact i j) (E.scalar_zeroOutside i j) p

lemma coefficientValue_jets4_eq_jets (E : ReferenceJacobiCompactExtensionRoom F K)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    coefficientValue 4 (E.jets4 i j p) = coefficientValue 3 (E.jets i j p) :=
  coefficientValue_commonSupportCoefficientFamily_order_eq 4 3 (E.scalar i j)
    (E.smooth i j) (E.spatialSupport i j) (E.spatialSupport_isCompact i j)
    (E.scalar_zeroOutside i j) p

def fiveHalfMultiplierFamily (E : ReferenceJacobiCompactExtensionRoom F K)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (5/2:ℝ) :=
  nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 (E.jets4 i j p)

lemma contDiff_fiveHalfMultiplierFamily (E : ReferenceJacobiCompactExtensionRoom F K)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) :
    ContDiff ℝ ∞ (E.fiveHalfMultiplierFamily hcalc hF hO hD τ0 i j) :=
  contDiff_nativeFiveHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (E.scalar i j) (E.smooth i j) (E.spatialSupport i j)
    (E.spatialSupport_isCompact i j) (E.scalar_zeroOutside i j)

lemma fiveHalfMultiplierFamily_threeHalf_compatibility
    (E : ReferenceJacobiCompactExtensionRoom F K)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).comp
      (E.fiveHalfMultiplierFamily hcalc hF hO hD τ0 i j p) =
    (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (E.jets i j p)).comp
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  exact sphereSobolevInclusionL_nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0
    (E.jets4 i j p) (E.jets i j p) (E.coefficientValue_jets4_eq_jets i j p) u

lemma eventually_fiveHalfMultiplierFamily_threeHalf_actual_eq
    (E : ReferenceJacobiCompactExtensionRoom F K)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ K) (i j : Fin 3) :
    ∀ᶠ t in 𝓝 p,
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).comp
        (E.fiveHalfMultiplierFamily hcalc hF hO hD τ0 i j t) =
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (F i j t)).comp
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  filter_upwards [E.eventually_nativeThreeHalfCoefficientMulL_jets_eq
    hcalc hF hO hD τ0 p hp i j] with t ht
  exact (E.fiveHalfMultiplierFamily_threeHalf_compatibility hcalc hF hO hD τ0 i j t).trans
    (congrArg (fun M : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) =>
      M.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) ht)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ReferenceJacobiCompactExtensionRoom
