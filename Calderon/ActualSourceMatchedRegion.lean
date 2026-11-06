import Calderon.ActualInitialExteriorKnownRegion
import Calderon.ActualRadiusTwoSourceSeparation
import Calderon.ActualFrontierOriginalSourceData

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature ConnectionError NativeSourceChartCalculus
open MetricOperator NormalCoordinatesFrame MetricVolume

/-- An actual local isometry matching every original exterior source response.
The total map is only required to have the stated properties on its domain. -/
structure ActualLocalSourceMatchedRegion
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2) where
  domain : Set R3
  domain_open : IsOpen domain
  domain_connected : IsConnected domain
  domain_room : domain ⊆ (radiusTwoOpens : Set R3)
  map : R3 → R3
  map_room : ∀ x ∈ domain, map x ∈ (radiusTwoOpens : Set R3)
  map_smooth : ContDiffOn ℝ ∞ map domain
  map_injective : InjOn map domain
  map_jacobian : ∀ x ∈ domain, IsUnit (coordinateJacobianMatrix map x).det
  metric_eq : EqOn (pullbackMetric g1 map) g2 domain
  source_eq : ∀ x ∈ domain,
    radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 (map x) =
      radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 x

/-- The manuscript's admissible matches additionally contain and fix the
entire initial exterior annulus. -/
structure ActualAdmissibleSourceMatch
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    extends ActualLocalSourceMatchedRegion hreg hcalc g1 g2 hg1 hg2 where
  exterior_subset : (exteriorAnnulusOpens : Set R3) ⊆ domain
  exterior_fixed : ∀ x ∈ (exteriorAnnulusOpens : Set R3), map x = x

/-- Source separation makes all actual local match maps compatible on overlap. -/
theorem actualLocalSourceMatchedRegion_maps_eq_on_overlap
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (A B : ActualLocalSourceMatchedRegion hreg hcalc g1 g2 hg1 hg2)
    (x : R3) (hA : x ∈ A.domain) (hB : x ∈ B.domain) : A.map x = B.map x := by
  have h := radiusTwoSourceEvaluationFamily_injective hreg hcalc hSep g1 hg1
    (a₁ := ⟨A.map x,A.map_room x hA⟩) (a₂ := ⟨B.map x,B.map_room x hB⟩)
    ((A.source_eq x hA).trans (B.source_eq x hB).symm)
  exact congrArg Subtype.val h

/-- Equal map germs give the same literal coordinate Jacobian. -/
theorem coordinateJacobianMatrix_eq_of_eventuallyEq
    (Phi Psi : R3 → R3) (x : R3) (h : Phi =ᶠ[nhds x] Psi) :
    coordinateJacobianMatrix Phi x = coordinateJacobianMatrix Psi x := by
  unfold coordinateJacobianMatrix
  rw [h.fderiv_eq]

/-- The actual metric pullback depends only on the map germ. -/
theorem pullbackMetric_eq_of_eventuallyEq
    (g : MatrixField) (Phi Psi : R3 → R3) (x : R3) (h : Phi =ᶠ[nhds x] Psi) :
    pullbackMetric g Phi x = pullbackMetric g Psi x := by
  unfold pullbackMetric
  rw [h.fderiv_eq,h.eq_of_nhds]

/-- Original exterior flatness and energy equality produce the genuine initial
admissible match, rather than taking its existence as a new premise. -/
def initialActualAdmissibleSourceMatch
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hEnergy : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g1 f = minimalEnergy g2 f) :
    ActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2 := by
  have hIdMap : operatorMatrixMap (ContinuousLinearMap.id ℝ R3) = (1 : Mat) :=
    matrixOperatorAlgEquiv.symm.map_one
  have hDId (x : R3) : fderiv ℝ (fun z : R3 => z) x = ContinuousLinearMap.id ℝ R3 :=
    (hasFDerivAt_id x).fderiv
  have hJac (x : R3) : coordinateJacobianMatrix (fun z : R3 => z) x = (1 : Mat) := by
    rw [coordinateJacobianMatrix_eq_operatorMatrixMap]
    simpa only [hDId] using hIdMap
  have hPull (x : R3) : pullbackMetric g1 (fun z : R3 => z) x = g1 x := by
    simp only [pullbackMetric,hDId,operatorMatrixMap_comp,operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField,hIdMap,Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one]
  refine {
    toActualLocalSourceMatchedRegion := {
      domain := (exteriorAnnulusOpens : Set R3)
      domain_open := exteriorAnnulusOpens.isOpen
      domain_connected := MixedKernelConstructionTask.isConnected_exteriorAnnulusOpens
      domain_room := exteriorAnnulusOpens_le_radiusTwoOpens
      map := fun x => x
      map_room := fun x hx => exteriorAnnulusOpens_le_radiusTwoOpens hx
      map_smooth := contDiff_id.contDiffOn
      map_injective := fun x hx y hy h => h
      map_jacobian := fun x hx => by rw [hJac,Matrix.det_one]; exact isUnit_one
      metric_eq := ?_
      source_eq := ?_ }
    exterior_subset := fun x hx => hx
    exterior_fixed := fun x hx => rfl }
  · intro x hx
    rw [hPull,hg1.euclidean_exterior x hx.1.le,hg2.euclidean_exterior x hx.1.le]
  · intro x hx
    exact radiusTwoSmoothSourceResponse_exterior_family_eq hreg hcalc g1 g2 hg1 hg2 hEnergy x hx

end OAI.AnisotropicCalderon.ExteriorSource
