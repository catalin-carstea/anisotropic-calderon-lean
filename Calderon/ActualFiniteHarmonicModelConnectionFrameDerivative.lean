import Calderon.ActualAngularFiniteCoefficientDerivative
import Calderon.ActualFiniteHarmonicModelReferenceWeights
import Calderon.ActualReferenceDDHigherSpectralGraphs

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  ActualFiniteHarmonicCore ActualReferenceParallelRaising AmbientReferenceCovariantCore AmbientReferenceRaising
  MovingFrameConnection SmoothMetricFrame SmoothSphereRotationProjection ActualNormalizedSphereRotation
  PrincipalCommutator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeConnectionFrameDerivativeFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeConnectionFrameDerivativeFunction

def nativeReferenceConnectionFrameDerivative
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (a b : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  (1/2 : ℝ) • ∑ u : Fin 3, ∑ v : Fin 3,
    coreScalar hO hD
      (referenceFrameDerivative g L lam a (fun y => referenceFrameConnectionCoefficient g L lam y
        (referenceMetricGramFrame g L (lam,y) b) u v))
      (contDiff_referenceFrameDerivative g hg L lam a _
        (contDiff_referenceFrameConnectionCoefficient_field g hg L lam _
          (contDiff_referenceMetricGramFrame_slice g hg L lam b) u v)) *
      coreRotation hO hD u v

lemma coreRotation_inner_skew
    (i j : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪coreRotation hO hD i j F x,G x⟫_ℝ = -⟪F x,coreRotation hO hD i j G x⟫_ℝ := by
  have hrot (U : smoothCompactFiniteSphereCore hO hD) :
      (U x,coreRotation hO hD i j U x) ∈ sphereRotationGraph hO hD i j := by
    intro n
    exact coreBlockOperator_coordinate hO hD (fun k => harmonicSphereRotation k i j) U x n
  exact sphereRotationGraph_inner_skew hO hD i j (F x) (coreRotation hO hD i j F x)
    (G x) (coreRotation hO hD i j G x) (hrot F) (hrot G)


lemma nativeReferenceConnectionFrameDerivative_normalized_apply
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (a b : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (fun y => normalizedReferenceAngularConnection hO hD g L lam y
        (referenceMetricGramFrame g L (lam,y) b)) x
      (coreWeightOperator hO hD (besselWeight 1) F x) =
        nativeReferenceConnectionFrameDerivative hO hD g hg L lam a b F x := by
  let c (z : Fin 3 × Fin 3) := fun y : R3 => referenceFrameConnectionCoefficient g L lam y
    (referenceMetricGramFrame g L (lam,y) b) z.1 z.2
  have hc (z : Fin 3 × Fin 3) : ContDiff ℝ ∞ (c z) :=
    contDiff_referenceFrameConnectionCoefficient_field g hg L lam _
      (contDiff_referenceMetricGramFrame_slice g hg L lam b) z.1 z.2
  have hcal := ActualAngularFiniteCoefficientDerivative.directionalFDeriv_fixed_scalar_sum
    (1/2 : ℝ) c hc (fun z => normalizedRotation hO hD z.1 z.2)
    (referenceMetricGramFrame g L (lam,x) a) x
  have he := congrArg (fun T : SphereL2 →L[ℝ] SphereL2 =>
    T (coreWeightOperator hO hD (besselWeight 1) F x)) hcal
  simpa only [normalizedReferenceAngularConnection,c,Fintype.sum_prod_type,
    nativeReferenceConnectionFrameDerivative,referenceFrameDerivative,directionalFDeriv,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,LinearMap.smul_apply,LinearMap.sum_apply,
    Module.End.mul_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
    Submodule.coe_sum,Submodule.coe_smul,Pi.smul_apply,Finset.sum_apply,
    coreRotation_apply_eq_normalizedRotation hO hD] using he


lemma nativeReferenceConnectionFrameDerivative_inner_skew
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (a b : Fin 3)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪nativeReferenceConnectionFrameDerivative hO hD g hg L lam a b F x,G x⟫_ℝ =
      -⟪F x,nativeReferenceConnectionFrameDerivative hO hD g hg L lam a b G x⟫_ℝ := by
  simp only [nativeReferenceConnectionFrameDerivative,LinearMap.smul_apply,LinearMap.sum_apply,
    Module.End.mul_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
    Submodule.coe_sum,Submodule.coe_smul,Pi.smul_apply,Finset.sum_apply,
    real_inner_smul_left,real_inner_smul_right,sum_inner,inner_sum]
  simp only [coreRotation_inner_skew hO hD,mul_neg,Finset.sum_neg_distrib]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
