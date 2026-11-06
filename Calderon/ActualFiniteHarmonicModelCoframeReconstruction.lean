import Calderon.ActualFiniteHarmonicModelFirstDefect
import Calderon.ActualPhysicalMixedNative
import Calderon.ActualFiniteHarmonicCoreScalarCentral

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  ActualModelCommutatorWords ActualPhysicalMixedNative ActualHorizontalNormBridge
  ReferenceDensityBounds PrincipalCommutator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev coframeReconstructionFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] coframeReconstructionFunction

def nativeReferenceCoFrameScalar
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (j a : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreScalar hO hD (fun y => referenceCoFrameEntry g L j a (lam,y))
    ((contDiff_referenceCoFrameEntry g hg L j a).comp (contDiff_const.prodMk contDiff_id))

lemma coreCoordinateDerivative_eq_coframe_horizontal_sub_connection
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (j : Fin 3) :
    coreDirectionalDerivative hO hD (coordinateDirection j) =
      ∑ a : Fin 3, nativeReferenceCoFrameScalar hO hD g hg L lam j a *
        (coreReferenceHorizontal hO hD g hg L lam a-nativeReferenceConnectionAction hO hD g hg L lam a) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  have hH (a : Fin 3) :
      (coreReferenceHorizontal hO hD g hg L lam a-nativeReferenceConnectionAction hO hD g hg L lam a) F x =
      ∑ k : Fin 3, referenceMetricGramFrame g L (lam,x) a k • coreDirectionalDerivative hO hD (coordinateDirection k) F x := by
    rw [coreReferenceHorizontal_eq_coefficients]
    simp only [LinearMap.add_apply,LinearMap.sub_apply,add_sub_cancel_right,LinearMap.sum_apply,
      Submodule.coe_sum,Finset.sum_apply,Module.End.mul_apply,nativeReferenceFrameScalar,coreScalar,
      LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk]
  have hdual (k : Fin 3) : (∑ a : Fin 3, referenceCoFrameEntry g L j a (lam,x)*referenceMetricGramFrame g L (lam,x) a k)=
      if j=k then 1 else 0 := referenceCoFrame_frameEntry_duality g hg L lam x j k
  change coreDirectionalDerivative hO hD (coordinateDirection j) F x =
    (∑ a : Fin 3, nativeReferenceCoFrameScalar hO hD g hg L lam j a *
      (coreReferenceHorizontal hO hD g hg L lam a-nativeReferenceConnectionAction hO hD g hg L lam a)) F x
  simp only [LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply,Module.End.mul_apply,
    nativeReferenceCoFrameScalar,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk]
  simp_rw [hH]
  symm
  calc
    _ = ∑ k : Fin 3, (∑ a : Fin 3, referenceCoFrameEntry g L j a (lam,x)*referenceMetricGramFrame g L (lam,x) a k) •
        coreDirectionalDerivative hO hD (coordinateDirection k) F x := by
      simp only [Finset.smul_sum,smul_smul,Finset.sum_smul]
      exact Finset.sum_comm
    _ = _ := by simp only [hdual]; simp [eq_comm]

lemma coreWeight_half_coordinateDerivative_eq_coframe_horizontal_sub_connection
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight (1/2:ℝ)) (coreDirectionalDerivative hO hD (coordinateDirection j) F) x =
      ∑ a : Fin 3, referenceCoFrameEntry g L j a (lam,x) •
        (coreWeightOperator hO hD (besselWeight (1/2:ℝ)) (coreReferenceHorizontal hO hD g hg L lam a F) x-
          coreWeightOperator hO hD (besselWeight (1/2:ℝ)) (nativeReferenceConnectionAction hO hD g hg L lam a F) x) := by
  let W := coreWeightOperator hO hD (besselWeight (1/2:ℝ))
  have hm (a : Fin 3) : W*(nativeReferenceCoFrameScalar hO hD g hg L lam j a *
      (coreReferenceHorizontal hO hD g hg L lam a-nativeReferenceConnectionAction hO hD g hg L lam a)) =
      nativeReferenceCoFrameScalar hO hD g hg L lam j a *
        (W*(coreReferenceHorizontal hO hD g hg L lam a-nativeReferenceConnectionAction hO hD g hg L lam a)) := by
    have hc := scalarCentral_coreWeightOperator hO hD (besselWeight (1/2:ℝ))
      (fun y => referenceCoFrameEntry g L j a (lam,y))
      ((contDiff_referenceCoFrameEntry g hg L j a).comp (contDiff_const.prodMk contDiff_id))
    change Commute W (nativeReferenceCoFrameScalar hO hD g hg L lam j a) at hc
    rw [← mul_assoc,hc.eq,mul_assoc]
  have heEnd := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => W*T)
    (coreCoordinateDerivative_eq_coframe_horizontal_sub_connection hO hD g hg L lam j)
  rw [Finset.mul_sum] at heEnd
  simp_rw [hm] at heEnd
  have he := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x) heEnd
  simpa only [LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply,Module.End.mul_apply,
    nativeReferenceCoFrameScalar,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
    LinearMap.sub_apply,map_sub,Submodule.coe_sub,Pi.sub_apply,W,smul_sub] using he

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
