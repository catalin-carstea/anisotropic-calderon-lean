import Calderon.ActualFiniteHarmonicModelFirstDefect
import Calderon.ActualNormalizedSecondDriftNativeAdjunction
import Calderon.ActualReferenceDDSpectralTransport

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition ActualFiniteHarmonicCore SpectralWeightedGraph
  BoundedAngularShift ActualNormalizedSecondDriftNativeAdjunction ActualReferenceDDSpectralTransport
  ActualReferenceDDNormalizedCoefficient ActualReferenceParallelRaising
  ActualPhysicalMixedFirst ActualPhysicalMixedReferenceCancellation AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection
  ReferenceDensityBounds NormalizedPrincipalMetric PrincipalCommutator ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev connectionSymmetricFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] connectionSymmetricFunction
lemma inverseDegreeMultiplier_adjoint_eq :
    ContinuousLinearMap.adjoint (inverseDegreeMultiplier hO hD) = inverseDegreeMultiplier hO hD := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact spectralGraph_inner_symm hO hD (besselWeight 1)
    (inverseDegreeMultiplier hO hD u) u (inverseDegreeMultiplier hO hD v) v
    (inverseDegreeMultiplier_besselGraph hO hD u)
    (inverseDegreeMultiplier_besselGraph hO hD v)

lemma normalizedReferenceAngularConnection_adjoint_core_apply
    (g : MatrixField) (L lam : ℝ) (x X : R3)
    (F : smoothCompactFiniteSphereCore hO hD) :
    ContinuousLinearMap.adjoint (normalizedReferenceAngularConnection hO hD g L lam x X) (F x) =
      -(normalizedReferenceAngularConnection hO hD g L lam x X (F x)) := by
  let A := normalizedReferenceAngularConnection hO hD g L lam x X
  let U := coreWeightOperator hO hD (besselWeight 1) F x
  have hU : (F x,U) ∈ sphereBesselGraph hO hD 1 :=
    coreWeightOperator_graph hO hD (besselWeight 1) F x
  have hAU : inverseDegreeMultiplier hO hD (A U) = A (F x) :=
    inverseDegreeMultiplier_of_besselGraph hO hD _ _
      (preservesSphereSpectralGraphs_normalizedReferenceAngularConnection hO hD g L lam x X
        (besselWeight 1) (F x) U hU)
  apply ext_inner_right ℝ
  intro v
  have hsk := normalizedReferenceAngularConnection_bessel_inner_skew hO hD g L lam x X
    (F x) U (inverseDegreeMultiplier hO hD v) v hU
    (inverseDegreeMultiplier_besselGraph hO hD v)
  have hi := ContinuousLinearMap.adjoint_inner_left (inverseDegreeMultiplier hO hD) v (A U)
  rw [inverseDegreeMultiplier_adjoint_eq hO hD] at hi
  change ⟪A U,inverseDegreeMultiplier hO hD v⟫_ℝ = -⟪F x,A v⟫_ℝ at hsk
  rw [← hi,hAU] at hsk
  change ⟪ContinuousLinearMap.adjoint A (F x),v⟫_ℝ = ⟪-(A (F x)),v⟫_ℝ
  rw [ContinuousLinearMap.adjoint_inner_left,inner_neg_left]
  linarith

lemma coreWeight_one_sub_self_eq_degree
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight 1) F x - F x = coreDegree hO hD F x := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  rw [map_sub]
  change SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k (coreWeightOperator hO hD (besselWeight 1) F x) -
      SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k (F x) =
    SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k (coreWeightOperator hO hD (fun l => (l : ℝ)) F x)
  rw [(coreWeightOperator_graph hO hD (besselWeight 1) F x) k,
    (coreWeightOperator_graph hO hD (fun l => (l : ℝ)) F x) k]
  simp only [besselWeight,Real.rpow_one,add_smul,one_smul]
  abel

lemma nativeReferenceFirst_symmetric_coreWeight_action
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j x +
      ContinuousLinearMap.adjoint (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j x))
      (coreWeightOperator hO hD (besselWeight 1) F x) =
    (2 * referenceRadius δ R p L x) • ∑ a : Fin 3, ∑ b : Fin 3,
      physicalMixedQFrameCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a b x •
        ((-(referenceConnectionFamily g1 L (lam,x) (referenceMetricGramFrame g1 L (lam,x) a)
          (referenceMetricGramFrame g1 L (lam,x) b)) j) • F x +
        (referenceFrameDerivative g1 L lam b (fun y => Real.log (referenceRadius δ R p L y)) x *
            referenceMetricGramFrame g1 L (lam,x) a j +
          referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)) x *
            referenceMetricGramFrame g1 L (lam,x) b j) • coreDegree hO hD F x) := by
  let I := inverseDegreeMultiplier hO hD
  let w := coreWeightOperator hO hD (besselWeight 1) F x
  let r := referenceRadius δ R p L x
  let q (a b : Fin 3) := physicalMixedQFrameCoefficient g1 L lam
    (referenceNormalizedPrincipalDifference g1 g2 L lam) a b x
  let e (a : Fin 3) := referenceMetricGramFrame g1 L (lam,x) a j
  let A (a : Fin 3) := normalizedReferenceAngularConnection hO hD g1 L lam x
    (referenceMetricGramFrame g1 L (lam,x) a)
  let gamma (a b : Fin 3) := (referenceConnectionFamily g1 L (lam,x)
    (referenceMetricGramFrame g1 L (lam,x) a) (referenceMetricGramFrame g1 L (lam,x) b)) j
  let eta (a b : Fin 3) :=
    referenceFrameDerivative g1 L lam b (fun y => Real.log (referenceRadius δ R p L y)) x * e a +
    referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)) x * e b
  let S (a b : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
    (-gamma a b) • I + e a • A b + e b • A a +
      eta a b • (ContinuousLinearMap.id ℝ SphereL2 - I)
  have hI : ContinuousLinearMap.adjoint I = I := inverseDegreeMultiplier_adjoint_eq hO hD
  have hi : I w = F x := inverseDegreeMultiplier_of_besselGraph hO hD _ _
    (coreWeightOperator_graph hO hD (besselWeight 1) F x)
  have hd : w - F x = coreDegree hO hD F x := coreWeight_one_sub_self_eq_degree hO hD F x
  have ha (a : Fin 3) : ContinuousLinearMap.adjoint (A a) w = -(A a w) :=
    normalizedReferenceAngularConnection_adjoint_core_apply hO hD g1 L lam x
      (referenceMetricGramFrame g1 L (lam,x) a) (coreWeightOperator hO hD (besselWeight 1) F)
  have hs (a b : Fin 3) : S a b w + ContinuousLinearMap.adjoint (S a b) w =
      (2 : ℝ) • ((-gamma a b) • F x + eta a b • coreDegree hO hD F x) := by
    dsimp only [S]
    simp only [map_add,map_sub,map_smulₛₗ,starRingEnd_apply,star_trivial,
      ContinuousLinearMap.adjoint_id,hI,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply]
    rw [ha a,ha b,hi,hd]
    module
  have hq (a b : Fin 3) : q a b • ((2 : ℝ) •
      ((-gamma a b) • F x + eta a b • coreDegree hO hD F x)) =
      (2 : ℝ) • (q a b • ((-gamma a b) • F x + eta a b • coreDegree hO hD F x)) :=
    smul_comm (q a b) (2 : ℝ) _
  unfold referenceWeightedFirstBaseNormalizedCoefficient
  change (r • ∑ a : Fin 3, ∑ b : Fin 3, q a b • S a b +
      ContinuousLinearMap.adjoint (r • ∑ a : Fin 3, ∑ b : Fin 3, q a b • S a b)) w =
    (2*r) • ∑ a : Fin 3, ∑ b : Fin 3,
      q a b • ((-gamma a b) • F x + eta a b • coreDegree hO hD F x)
  simp only [map_smulₛₗ,map_sum,starRingEnd_apply,star_trivial,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply]
  rw [← smul_add,← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib,← smul_add,hs,hq,← Finset.smul_sum]
  rw [smul_smul,mul_comm r 2]


end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
