import Calderon.NativeOrderOneCoefficientMultiplier
import Calderon.SphereSobolevCompatibleInterpolationTopology
import Calderon.ClosedCoefficientMultiplier

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma coefficientValue_commonSupportCoefficientFamily_order_eq
    (r t : ℕ) (g : E × R3 → ℝ) (hg : ContDiff ℝ ∞ g)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → g (p,x) = 0) (p : E) :
    coefficientValue r (commonSupportCoefficientFamily r g hg K hK hz p) =
      coefficientValue t (commonSupportCoefficientFamily t g hg K hK hz p) := by
  funext x
  exact (coefficientValue_commonSupportCoefficientFamily r g hg K hK hz p x).trans
    (coefficientValue_commonSupportCoefficientFamily t g hg K hK hz p x).symm

lemma contDiff_nativeThreeHalfCoefficientMulL_commonSupport
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (g : E × R3 → ℝ) (hg : ContDiff ℝ ∞ g)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → g (p,x) = 0) :
    ContDiff ℝ ∞ (fun p : E => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (commonSupportCoefficientFamily 3 g hg K hK hz p)) := by
  unfold nativeThreeHalfCoefficientMulL
  exact contDiff_const.clm_comp
    ((contDiff_commonSupport_actual_coefficientMultiplier hcalc 2 g hg K hK hz).clm_comp contDiff_const)

lemma contDiff_nativeOrderOneCoefficientMulL_commonSupport
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (g : E × R3 → ℝ) (hg : ContDiff ℝ ∞ g)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → g (p,x) = 0) :
    ContDiff ℝ ∞ (fun p : E => nativeOrderOneCoefficientMulL hcalc hF hO hD τ0
      (commonSupportCoefficientFamily 3 g hg K hK hz p)
      (commonSupportCoefficientFamily 2 g hg K hK hz p)
      (coefficientValue_commonSupportCoefficientFamily_order_eq 3 2 g hg K hK hz p)) := by
  let L : E → (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) := fun p =>
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 (commonSupportCoefficientFamily 2 g hg K hK hz p)
  let H : E → (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)) := fun p =>
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (commonSupportCoefficientFamily 3 g hg K hK hz p)
  let hc (p : E) := nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0
    (commonSupportCoefficientFamily 3 g hg K hK hz p)
    (commonSupportCoefficientFamily 2 g hg K hK hz p)
    (coefficientValue_commonSupportCoefficientFamily_order_eq 3 2 g hg K hK hz p)
  let T (p : E) := sphereSobolevSameOrderEndpoints (L p) (H p) (hc p)
  let raw : E → SphereSobolevEndpointPair := fun p => (T p).val
  have hL : ContDiff ℝ ∞ L := contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 g hg K hK hz
  have hH : ContDiff ℝ ∞ H := contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 g hg K hK hz
  have hRaw : ContDiff ℝ ∞ raw := by
    change ContDiff ℝ ∞ (fun p : E =>
      ((sphereSobolevBesselOrderL (1/2:ℝ) (-1/2:ℝ)).comp (L p),
        (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)).comp (H p)))
    exact (contDiff_const.clm_comp hL).prodMk (contDiff_const.clm_comp hH)
  have hT : ∀ p ∈ (Set.univ : Set E), raw p ∈ sphereSobolevCompatibleEndpoints :=
    fun p hp => (T p).property
  have hMid : ContDiff ℝ ∞ (fun p : E => sphereSobolevCompatibleMidpointL (T p)) := by
    apply contDiffOn_univ.mp
    apply contDiffOn_of_eq_compatibleInterpolation raw Set.univ isOpen_univ hT hRaw.contDiffOn
    intro p hp
    rfl
  exact contDiff_const.clm_comp hMid

end OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier
#print axioms OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier.coefficientValue_commonSupportCoefficientFamily_order_eq
#print axioms OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier.contDiff_nativeThreeHalfCoefficientMulL_commonSupport
#print axioms OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier.contDiff_nativeOrderOneCoefficientMulL_commonSupport
