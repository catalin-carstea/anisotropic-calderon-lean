import Calderon.ActualFiniteHarmonicModelSecondAngularSymmetricCore

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift BalancedAngularShift
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualReferenceDDHigherSpectralGraphs ActualReferenceDDSpectralTransport ActualReferenceDDNormalizedCoefficient
  ActualReferenceParallelRaising ActualNormalizedSphereRotation ActualScalarPrincipalAdjoint NaturalAngularAdjoint
  ActualNormalizedSecondModelErrorAssembly ActualNormalizedSecondDriftNativeAdjunction
  ActualNormalizedSecondDriftDefectCoefficients ActualNormalizedSecondDriftDefectWeightedJets ActualNormalizedSecondMetricDrift
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  ReferenceDensityBounds NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  SmoothMetricFrame MovingFrameConnection PrincipalCommutator ConformalDepth SectionFiveErrorForms
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeWSymmetricFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWSymmetricFunction
def nativeWSecondPairing
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
  (innerSL ℝ (G x)).comp (ContinuousLinearMap.apply ℝ SphereL2
      (coreWeightOperator hO hD (besselWeight 2) F x)) +
    (innerSL ℝ (F x)).comp (ContinuousLinearMap.apply ℝ SphereL2
      (coreWeightOperator hO hD (besselWeight 2) G x))

def nativeWHalfPairing
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
  (innerSL ℝ (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)).comp
    (ContinuousLinearMap.apply ℝ SphereL2 (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x))
lemma nativeW_pairing_inverse_square
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3)
    : nativeWSecondPairing hO hD F G x ((inverseDegreeMultiplier hO hD).comp (inverseDegreeMultiplier hO hD)) = (2 : ℝ)*nativeWHalfPairing hO hD F G x (inverseDegreeMultiplier hO hD) := by
  let u := F x
  let v := G x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let v1 := coreWeightOperator hO hD (besselWeight 1) G x
  let u2 := coreWeightOperator hO hD (besselWeight 2) F x
  let v2 := coreWeightOperator hO hD (besselWeight 2) G x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let I := inverseDegreeMultiplier hO hD
  let Id := ContinuousLinearMap.id ℝ SphereL2
  have hu1 : (u,u1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) F x
  have hv1 : (v,v1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) G x
  have hu12 : (u1,u2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) F x,coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x
  have hv12 : (v1,v2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) G x,coreWeightOperator hO hD (besselWeight 2) G x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD G x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) G) x
  have huh : (u,uh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x
  have hvh : (v,vh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x
  have hub : (uh,u1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hu1 k,huh k,smul_smul,← besselWeight_add]
    norm_num
  have hvb : (vh,v1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hv1 k,hvh k,smul_smul,← besselWeight_add]
    norm_num
  have hi2u : I u2 = u1 := inverseDegreeMultiplier_of_besselGraph hO hD u1 u2 hu12
  have hi2v : I v2 = v1 := inverseDegreeMultiplier_of_besselGraph hO hD v1 v2 hv12
  have hi1u : I u1 = u := inverseDegreeMultiplier_of_besselGraph hO hD u u1 hu1
  have hi1v : I v1 = v := inverseDegreeMultiplier_of_besselGraph hO hD v v1 hv1
  let J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ SphereL2 u2) +
      (innerSL ℝ u).comp (ContinuousLinearMap.apply ℝ SphereL2 v2)
  let Q : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ vh).comp (ContinuousLinearMap.apply ℝ SphereL2 uh)
  have hJ (A : SphereL2 →L[ℝ] SphereL2) : J A = ⟪A u2,v⟫_ℝ+⟪u,A v2⟫_ℝ := by
    change ⟪v,A u2⟫_ℝ+⟪u,A v2⟫_ℝ = _
    rw [real_inner_comm (A u2) v]
  have hQ (A : SphereL2 →L[ℝ] SphereL2) : Q A = ⟪A uh,vh⟫_ℝ := by
    change ⟪vh,A uh⟫_ℝ = _
    rw [real_inner_comm (A uh) vh]
  have hdiag (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪A u1,v⟫_ℝ = ⟪A uh,vh⟫_ℝ :=
    spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ)) (A uh) (A u1) v vh (hA _ uh u1 hub) hvh
  have hdiagSwap (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪u,A v1⟫_ℝ = ⟪uh,A vh⟫_ℝ := by
    have ht := spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ))
      (A vh) (A v1) u uh (hA _ vh v1 hvb) huh
    simpa only [real_inner_comm] using ht
  have hQ_I : Q I = ⟪u,v⟫_ℝ := by
    rw [hQ,← hdiag I (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD),hi1u]
  change J ((I).comp (I)) = (2 : ℝ)*Q (I)
  rw [hJ,hQ_I]
  simp only [ContinuousLinearMap.comp_apply,hi2u,hi2v,hi1u,hi1v]
  ring


lemma nativeW_pairing_profile
    (hF : SphereFischerInner)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (a : Fin 3)
    : nativeWSecondPairing hO hD F G x ((normalizedDerivative hF hO hD a).comp ((ContinuousLinearMap.id ℝ SphereL2)-(2 : ℝ) • (inverseDegreeMultiplier hO hD))) =
    nativeWSecondPairing hO hD F G x ((normalizedRaising hF hO hD a).comp ((ContinuousLinearMap.id ℝ SphereL2)-(inverseDegreeMultiplier hO hD))) := by
  let u := F x
  let v := G x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let v1 := coreWeightOperator hO hD (besselWeight 1) G x
  let u2 := coreWeightOperator hO hD (besselWeight 2) F x
  let v2 := coreWeightOperator hO hD (besselWeight 2) G x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let I := inverseDegreeMultiplier hO hD
  let Id := ContinuousLinearMap.id ℝ SphereL2
  have hu1 : (u,u1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) F x
  have hv1 : (v,v1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) G x
  have hu12 : (u1,u2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) F x,coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x
  have hv12 : (v1,v2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) G x,coreWeightOperator hO hD (besselWeight 2) G x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD G x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) G) x
  have huh : (u,uh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x
  have hvh : (v,vh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x
  have hub : (uh,u1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hu1 k,huh k,smul_smul,← besselWeight_add]
    norm_num
  have hvb : (vh,v1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hv1 k,hvh k,smul_smul,← besselWeight_add]
    norm_num
  have hi2u : I u2 = u1 := inverseDegreeMultiplier_of_besselGraph hO hD u1 u2 hu12
  have hi2v : I v2 = v1 := inverseDegreeMultiplier_of_besselGraph hO hD v1 v2 hv12
  have hi1u : I u1 = u := inverseDegreeMultiplier_of_besselGraph hO hD u u1 hu1
  have hi1v : I v1 = v := inverseDegreeMultiplier_of_besselGraph hO hD v v1 hv1
  let J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ SphereL2 u2) +
      (innerSL ℝ u).comp (ContinuousLinearMap.apply ℝ SphereL2 v2)
  let Q : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ vh).comp (ContinuousLinearMap.apply ℝ SphereL2 uh)
  have hJ (A : SphereL2 →L[ℝ] SphereL2) : J A = ⟪A u2,v⟫_ℝ+⟪u,A v2⟫_ℝ := by
    change ⟪v,A u2⟫_ℝ+⟪u,A v2⟫_ℝ = _
    rw [real_inner_comm (A u2) v]
  have hQ (A : SphereL2 →L[ℝ] SphereL2) : Q A = ⟪A uh,vh⟫_ℝ := by
    change ⟪vh,A uh⟫_ℝ = _
    rw [real_inner_comm (A uh) vh]
  have hdiag (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪A u1,v⟫_ℝ = ⟪A uh,vh⟫_ℝ :=
    spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ)) (A uh) (A u1) v vh (hA _ uh u1 hub) hvh
  have hdiagSwap (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪u,A v1⟫_ℝ = ⟪uh,A vh⟫_ℝ := by
    have ht := spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ))
      (A vh) (A v1) u uh (hA _ vh v1 hvb) huh
    simpa only [real_inner_comm] using ht
  have hQ_I : Q I = ⟪u,v⟫_ℝ := by
    rw [hQ,← hdiag I (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD),hi1u]
  have hJadjDiff (A B : SphereL2 →L[ℝ] SphereL2)
      (hAB : ⟪A u2,v⟫_ℝ = ⟪u,B v2⟫_ℝ) (hBA : ⟪A v2,u⟫_ℝ = ⟪v,B u2⟫_ℝ) :
      J (A-B) = 0 := by
    rw [hJ]
    simp only [ContinuousLinearMap.sub_apply,inner_sub_left,inner_sub_right]
    have ht := hBA
    rw [real_inner_comm u (A v2),real_inner_comm (B u2) v] at ht
    rw [hAB,ht]
    ring
  change J ((normalizedDerivative hF hO hD a).comp ((Id)-(2 : ℝ) • (I))) =
    J ((normalizedRaising hF hO hD a).comp ((Id)-(I)))
  have ht := hJadjDiff ((normalizedDerivative hF hO hD a).comp (Id-(2 : ℝ) • I))
    ((normalizedRaising hF hO hD a).comp (Id-I))
    (by simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,Id,hi2u,hi2v] using nativeW_profile_basis_inner_adjoint hO hD hF a F G x)
    (by simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,Id,hi2u,hi2v] using nativeW_profile_basis_inner_adjoint hO hD hF a G F x)
  rw [map_sub] at ht
  linarith


lemma nativeW_pairing_connection
    (hF : SphereFischerInner)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (a b c : Fin 3)
    : nativeWSecondPairing hO hD F G x ((normalizedRotation hO hD b c).comp ((normalizedDerivative hF hO hD a).comp ((ContinuousLinearMap.id ℝ SphereL2)-(inverseDegreeMultiplier hO hD)))) =
    -nativeWSecondPairing hO hD F G x ((normalizedRaising hF hO hD a).comp (normalizedRotation hO hD b c)) := by
  let u := F x
  let v := G x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let v1 := coreWeightOperator hO hD (besselWeight 1) G x
  let u2 := coreWeightOperator hO hD (besselWeight 2) F x
  let v2 := coreWeightOperator hO hD (besselWeight 2) G x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let I := inverseDegreeMultiplier hO hD
  let Id := ContinuousLinearMap.id ℝ SphereL2
  have hu1 : (u,u1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) F x
  have hv1 : (v,v1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) G x
  have hu12 : (u1,u2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) F x,coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x
  have hv12 : (v1,v2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) G x,coreWeightOperator hO hD (besselWeight 2) G x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD G x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) G) x
  have huh : (u,uh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x
  have hvh : (v,vh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x
  have hub : (uh,u1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hu1 k,huh k,smul_smul,← besselWeight_add]
    norm_num
  have hvb : (vh,v1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hv1 k,hvh k,smul_smul,← besselWeight_add]
    norm_num
  have hi2u : I u2 = u1 := inverseDegreeMultiplier_of_besselGraph hO hD u1 u2 hu12
  have hi2v : I v2 = v1 := inverseDegreeMultiplier_of_besselGraph hO hD v1 v2 hv12
  have hi1u : I u1 = u := inverseDegreeMultiplier_of_besselGraph hO hD u u1 hu1
  have hi1v : I v1 = v := inverseDegreeMultiplier_of_besselGraph hO hD v v1 hv1
  let J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ SphereL2 u2) +
      (innerSL ℝ u).comp (ContinuousLinearMap.apply ℝ SphereL2 v2)
  let Q : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ vh).comp (ContinuousLinearMap.apply ℝ SphereL2 uh)
  have hJ (A : SphereL2 →L[ℝ] SphereL2) : J A = ⟪A u2,v⟫_ℝ+⟪u,A v2⟫_ℝ := by
    change ⟪v,A u2⟫_ℝ+⟪u,A v2⟫_ℝ = _
    rw [real_inner_comm (A u2) v]
  have hQ (A : SphereL2 →L[ℝ] SphereL2) : Q A = ⟪A uh,vh⟫_ℝ := by
    change ⟪vh,A uh⟫_ℝ = _
    rw [real_inner_comm (A uh) vh]
  have hdiag (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪A u1,v⟫_ℝ = ⟪A uh,vh⟫_ℝ :=
    spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ)) (A uh) (A u1) v vh (hA _ uh u1 hub) hvh
  have hdiagSwap (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪u,A v1⟫_ℝ = ⟪uh,A vh⟫_ℝ := by
    have ht := spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ))
      (A vh) (A v1) u uh (hA _ vh v1 hvb) huh
    simpa only [real_inner_comm] using ht
  have hQ_I : Q I = ⟪u,v⟫_ℝ := by
    rw [hQ,← hdiag I (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD),hi1u]
  have hJadjDiff (A B : SphereL2 →L[ℝ] SphereL2)
      (hAB : ⟪A u2,v⟫_ℝ = ⟪u,B v2⟫_ℝ) (hBA : ⟪A v2,u⟫_ℝ = ⟪v,B u2⟫_ℝ) :
      J (A-B) = 0 := by
    rw [hJ]
    simp only [ContinuousLinearMap.sub_apply,inner_sub_left,inner_sub_right]
    have ht := hBA
    rw [real_inner_comm u (A v2),real_inner_comm (B u2) v] at ht
    rw [hAB,ht]
    ring
  change J ((normalizedRotation hO hD b c).comp ((normalizedDerivative hF hO hD a).comp ((Id)-(I)))) =
    -J ((normalizedRaising hF hO hD a).comp (normalizedRotation hO hD b c))
  let A := (normalizedRotation hO hD b c).comp ((normalizedDerivative hF hO hD a).comp (Id-I))
  let B := (normalizedRaising hF hO hD a).comp (normalizedRotation hO hD b c)
  have ht := hJadjDiff (-A) B
    (by simpa only [A,B,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply,Id,hi2u,hi2v,inner_neg_left,neg_neg] using
      congrArg Neg.neg (nativeW_connection_basis_inner_adjoint hO hD hF a b c F G x))
    (by simpa only [A,B,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply,Id,hi2u,hi2v,inner_neg_left,neg_neg] using
      congrArg Neg.neg (nativeW_connection_basis_inner_adjoint hO hD hF a b c G F x))
  rw [map_sub,map_neg] at ht
  dsimp only [A,B] at ht
  linarith


lemma nativeW_pairing_pure
    (hF : SphereFischerInner)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (a b : Fin 3)
    : nativeWSecondPairing hO hD F G x ((normalizedDerivative hF hO hD b).comp ((normalizedDerivative hF hO hD a).comp ((ContinuousLinearMap.id ℝ SphereL2)-(inverseDegreeMultiplier hO hD)))) =
    nativeWSecondPairing hO hD F G x ((normalizedRaising hF hO hD a).comp ((normalizedRaising hF hO hD b).comp ((ContinuousLinearMap.id ℝ SphereL2)+(inverseDegreeMultiplier hO hD)))) := by
  let u := F x
  let v := G x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let v1 := coreWeightOperator hO hD (besselWeight 1) G x
  let u2 := coreWeightOperator hO hD (besselWeight 2) F x
  let v2 := coreWeightOperator hO hD (besselWeight 2) G x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let I := inverseDegreeMultiplier hO hD
  let Id := ContinuousLinearMap.id ℝ SphereL2
  have hu1 : (u,u1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) F x
  have hv1 : (v,v1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) G x
  have hu12 : (u1,u2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) F x,coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x
  have hv12 : (v1,v2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) G x,coreWeightOperator hO hD (besselWeight 2) G x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD G x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) G) x
  have huh : (u,uh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x
  have hvh : (v,vh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x
  have hub : (uh,u1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hu1 k,huh k,smul_smul,← besselWeight_add]
    norm_num
  have hvb : (vh,v1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hv1 k,hvh k,smul_smul,← besselWeight_add]
    norm_num
  have hi2u : I u2 = u1 := inverseDegreeMultiplier_of_besselGraph hO hD u1 u2 hu12
  have hi2v : I v2 = v1 := inverseDegreeMultiplier_of_besselGraph hO hD v1 v2 hv12
  have hi1u : I u1 = u := inverseDegreeMultiplier_of_besselGraph hO hD u u1 hu1
  have hi1v : I v1 = v := inverseDegreeMultiplier_of_besselGraph hO hD v v1 hv1
  let J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ SphereL2 u2) +
      (innerSL ℝ u).comp (ContinuousLinearMap.apply ℝ SphereL2 v2)
  let Q : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ vh).comp (ContinuousLinearMap.apply ℝ SphereL2 uh)
  have hJ (A : SphereL2 →L[ℝ] SphereL2) : J A = ⟪A u2,v⟫_ℝ+⟪u,A v2⟫_ℝ := by
    change ⟪v,A u2⟫_ℝ+⟪u,A v2⟫_ℝ = _
    rw [real_inner_comm (A u2) v]
  have hQ (A : SphereL2 →L[ℝ] SphereL2) : Q A = ⟪A uh,vh⟫_ℝ := by
    change ⟪vh,A uh⟫_ℝ = _
    rw [real_inner_comm (A uh) vh]
  have hdiag (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪A u1,v⟫_ℝ = ⟪A uh,vh⟫_ℝ :=
    spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ)) (A uh) (A u1) v vh (hA _ uh u1 hub) hvh
  have hdiagSwap (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪u,A v1⟫_ℝ = ⟪uh,A vh⟫_ℝ := by
    have ht := spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ))
      (A vh) (A v1) u uh (hA _ vh v1 hvb) huh
    simpa only [real_inner_comm] using ht
  have hQ_I : Q I = ⟪u,v⟫_ℝ := by
    rw [hQ,← hdiag I (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD),hi1u]
  have hJadjDiff (A B : SphereL2 →L[ℝ] SphereL2)
      (hAB : ⟪A u2,v⟫_ℝ = ⟪u,B v2⟫_ℝ) (hBA : ⟪A v2,u⟫_ℝ = ⟪v,B u2⟫_ℝ) :
      J (A-B) = 0 := by
    rw [hJ]
    simp only [ContinuousLinearMap.sub_apply,inner_sub_left,inner_sub_right]
    have ht := hBA
    rw [real_inner_comm u (A v2),real_inner_comm (B u2) v] at ht
    rw [hAB,ht]
    ring
  change J ((normalizedDerivative hF hO hD b).comp ((normalizedDerivative hF hO hD a).comp ((Id)-(I)))) =
    J ((normalizedRaising hF hO hD a).comp ((normalizedRaising hF hO hD b).comp ((Id)+(I))))
  have ht := hJadjDiff
    ((normalizedDerivative hF hO hD b).comp ((normalizedDerivative hF hO hD a).comp (Id-I)))
    ((normalizedRaising hF hO hD a).comp ((normalizedRaising hF hO hD b).comp (Id+I)))
    (by simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply,Id,hi2u,hi2v] using nativeW_pure_basis_inner_adjoint hO hD hF a b F G x)
    (by simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply,Id,hi2u,hi2v] using nativeW_pure_basis_inner_adjoint hO hD hF a b G F x)
  rw [map_sub] at ht
  linarith


lemma nativeW_pairing_rotation
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (b c : Fin 3)
    : nativeWSecondPairing hO hD F G x ((normalizedRotation hO hD b c).comp (inverseDegreeMultiplier hO hD)) = 0 := by
  let u := F x
  let v := G x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let v1 := coreWeightOperator hO hD (besselWeight 1) G x
  let u2 := coreWeightOperator hO hD (besselWeight 2) F x
  let v2 := coreWeightOperator hO hD (besselWeight 2) G x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let I := inverseDegreeMultiplier hO hD
  let Id := ContinuousLinearMap.id ℝ SphereL2
  have hu1 : (u,u1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) F x
  have hv1 : (v,v1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) G x
  have hu12 : (u1,u2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) F x,coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x
  have hv12 : (v1,v2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) G x,coreWeightOperator hO hD (besselWeight 2) G x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD G x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) G) x
  have huh : (u,uh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x
  have hvh : (v,vh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x
  have hub : (uh,u1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hu1 k,huh k,smul_smul,← besselWeight_add]
    norm_num
  have hvb : (vh,v1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hv1 k,hvh k,smul_smul,← besselWeight_add]
    norm_num
  have hi2u : I u2 = u1 := inverseDegreeMultiplier_of_besselGraph hO hD u1 u2 hu12
  have hi2v : I v2 = v1 := inverseDegreeMultiplier_of_besselGraph hO hD v1 v2 hv12
  have hi1u : I u1 = u := inverseDegreeMultiplier_of_besselGraph hO hD u u1 hu1
  have hi1v : I v1 = v := inverseDegreeMultiplier_of_besselGraph hO hD v v1 hv1
  let J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ SphereL2 u2) +
      (innerSL ℝ u).comp (ContinuousLinearMap.apply ℝ SphereL2 v2)
  let Q : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ vh).comp (ContinuousLinearMap.apply ℝ SphereL2 uh)
  have hJ (A : SphereL2 →L[ℝ] SphereL2) : J A = ⟪A u2,v⟫_ℝ+⟪u,A v2⟫_ℝ := by
    change ⟪v,A u2⟫_ℝ+⟪u,A v2⟫_ℝ = _
    rw [real_inner_comm (A u2) v]
  have hQ (A : SphereL2 →L[ℝ] SphereL2) : Q A = ⟪A uh,vh⟫_ℝ := by
    change ⟪vh,A uh⟫_ℝ = _
    rw [real_inner_comm (A uh) vh]
  have hdiag (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪A u1,v⟫_ℝ = ⟪A uh,vh⟫_ℝ :=
    spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ)) (A uh) (A u1) v vh (hA _ uh u1 hub) hvh
  have hdiagSwap (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪u,A v1⟫_ℝ = ⟪uh,A vh⟫_ℝ := by
    have ht := spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ))
      (A vh) (A v1) u uh (hA _ vh v1 hvb) huh
    simpa only [real_inner_comm] using ht
  have hQ_I : Q I = ⟪u,v⟫_ℝ := by
    rw [hQ,← hdiag I (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD),hi1u]
  change J ((normalizedRotation hO hD b c).comp (I)) = 0
  have ht := sphereRotationGraph_inner_skew hO hD b c u (normalizedRotation hO hD b c u1)
    v (normalizedRotation hO hD b c v1)
    (normalizedRotation_graph hO hD b c u u1 hu1) (normalizedRotation_graph hO hD b c v v1 hv1)
  rw [hJ]
  simp only [ContinuousLinearMap.comp_apply,hi2u,hi2v]
  linarith


lemma nativeW_pairing_density
    (hF : SphereFischerInner)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (a : Fin 3)
    : nativeWSecondPairing hO hD F G x ((normalizedDerivative hF hO hD a).comp (inverseDegreeMultiplier hO hD)) =
    nativeWHalfPairing hO hD F G x (balancedDerivative hF hO hD a+balancedRaising hF hO hD a) := by
  let u := F x
  let v := G x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let v1 := coreWeightOperator hO hD (besselWeight 1) G x
  let u2 := coreWeightOperator hO hD (besselWeight 2) F x
  let v2 := coreWeightOperator hO hD (besselWeight 2) G x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let I := inverseDegreeMultiplier hO hD
  let Id := ContinuousLinearMap.id ℝ SphereL2
  have hu1 : (u,u1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) F x
  have hv1 : (v,v1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) G x
  have hu12 : (u1,u2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) F x,coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x
  have hv12 : (v1,v2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) G x,coreWeightOperator hO hD (besselWeight 2) G x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD G x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) G) x
  have huh : (u,uh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x
  have hvh : (v,vh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x
  have hub : (uh,u1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hu1 k,huh k,smul_smul,← besselWeight_add]
    norm_num
  have hvb : (vh,v1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hv1 k,hvh k,smul_smul,← besselWeight_add]
    norm_num
  have hi2u : I u2 = u1 := inverseDegreeMultiplier_of_besselGraph hO hD u1 u2 hu12
  have hi2v : I v2 = v1 := inverseDegreeMultiplier_of_besselGraph hO hD v1 v2 hv12
  have hi1u : I u1 = u := inverseDegreeMultiplier_of_besselGraph hO hD u u1 hu1
  have hi1v : I v1 = v := inverseDegreeMultiplier_of_besselGraph hO hD v v1 hv1
  let J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ SphereL2 u2) +
      (innerSL ℝ u).comp (ContinuousLinearMap.apply ℝ SphereL2 v2)
  let Q : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ vh).comp (ContinuousLinearMap.apply ℝ SphereL2 uh)
  have hJ (A : SphereL2 →L[ℝ] SphereL2) : J A = ⟪A u2,v⟫_ℝ+⟪u,A v2⟫_ℝ := by
    change ⟪v,A u2⟫_ℝ+⟪u,A v2⟫_ℝ = _
    rw [real_inner_comm (A u2) v]
  have hQ (A : SphereL2 →L[ℝ] SphereL2) : Q A = ⟪A uh,vh⟫_ℝ := by
    change ⟪vh,A uh⟫_ℝ = _
    rw [real_inner_comm (A uh) vh]
  have hdiag (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪A u1,v⟫_ℝ = ⟪A uh,vh⟫_ℝ :=
    spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ)) (A uh) (A u1) v vh (hA _ uh u1 hub) hvh
  have hdiagSwap (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪u,A v1⟫_ℝ = ⟪uh,A vh⟫_ℝ := by
    have ht := spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ))
      (A vh) (A v1) u uh (hA _ vh v1 hvb) huh
    simpa only [real_inner_comm] using ht
  have hQ_I : Q I = ⟪u,v⟫_ℝ := by
    rw [hQ,← hdiag I (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD),hi1u]
  change J ((normalizedDerivative hF hO hD a).comp (I)) =
    Q (balancedDerivative hF hO hD a+balancedRaising hF hO hD a)
  have hd := balancedDerivative_inner_realization hF hO hD a u uh (normalizedDerivative hF hO hD a u1)
    v vh huh (normalizedDerivative_graph hF hO hD a u u1 hu1) hvh
  have hr := balancedRaising_inner_realization hF hO hD a u uh (normalizedRaising hF hO hD a u1)
    v vh huh (normalizedRaising_graph hF hO hD a u u1 hu1) hvh
  have ha := AngularShiftGraph.sphereDerivativeGraph_inner_adjoint hF hO hD a v (normalizedDerivative hF hO hD a v1)
    u (normalizedRaising hF hO hD a u1)
    (normalizedDerivative_graph hF hO hD a v v1 hv1) (normalizedRaising_graph hF hO hD a u u1 hu1)
  rw [real_inner_comm u (normalizedDerivative hF hO hD a v1),
    real_inner_comm (normalizedRaising hF hO hD a u1) v] at ha
  rw [hJ,hQ]
  simp only [ContinuousLinearMap.comp_apply,hi2u,hi2v,ContinuousLinearMap.add_apply,inner_add_left]
  rw [ha,hd,hr]


lemma nativeW_pairing_diagonal
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A)
    : nativeWSecondPairing hO hD F G x (A.comp (inverseDegreeMultiplier hO hD)) = nativeWHalfPairing hO hD F G x (A+ContinuousLinearMap.adjoint A) := by
  let u := F x
  let v := G x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let v1 := coreWeightOperator hO hD (besselWeight 1) G x
  let u2 := coreWeightOperator hO hD (besselWeight 2) F x
  let v2 := coreWeightOperator hO hD (besselWeight 2) G x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let I := inverseDegreeMultiplier hO hD
  let Id := ContinuousLinearMap.id ℝ SphereL2
  have hu1 : (u,u1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) F x
  have hv1 : (v,v1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) G x
  have hu12 : (u1,u2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) F x,coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x
  have hv12 : (v1,v2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) G x,coreWeightOperator hO hD (besselWeight 2) G x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD G x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) G) x
  have huh : (u,uh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x
  have hvh : (v,vh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x
  have hub : (uh,u1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hu1 k,huh k,smul_smul,← besselWeight_add]
    norm_num
  have hvb : (vh,v1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hv1 k,hvh k,smul_smul,← besselWeight_add]
    norm_num
  have hi2u : I u2 = u1 := inverseDegreeMultiplier_of_besselGraph hO hD u1 u2 hu12
  have hi2v : I v2 = v1 := inverseDegreeMultiplier_of_besselGraph hO hD v1 v2 hv12
  have hi1u : I u1 = u := inverseDegreeMultiplier_of_besselGraph hO hD u u1 hu1
  have hi1v : I v1 = v := inverseDegreeMultiplier_of_besselGraph hO hD v v1 hv1
  let J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ SphereL2 u2) +
      (innerSL ℝ u).comp (ContinuousLinearMap.apply ℝ SphereL2 v2)
  let Q : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ vh).comp (ContinuousLinearMap.apply ℝ SphereL2 uh)
  have hJ (A : SphereL2 →L[ℝ] SphereL2) : J A = ⟪A u2,v⟫_ℝ+⟪u,A v2⟫_ℝ := by
    change ⟪v,A u2⟫_ℝ+⟪u,A v2⟫_ℝ = _
    rw [real_inner_comm (A u2) v]
  have hQ (A : SphereL2 →L[ℝ] SphereL2) : Q A = ⟪A uh,vh⟫_ℝ := by
    change ⟪vh,A uh⟫_ℝ = _
    rw [real_inner_comm (A uh) vh]
  have hdiag (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪A u1,v⟫_ℝ = ⟪A uh,vh⟫_ℝ :=
    spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ)) (A uh) (A u1) v vh (hA _ uh u1 hub) hvh
  have hdiagSwap (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪u,A v1⟫_ℝ = ⟪uh,A vh⟫_ℝ := by
    have ht := spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ))
      (A vh) (A v1) u uh (hA _ vh v1 hvb) huh
    simpa only [real_inner_comm] using ht
  have hQ_I : Q I = ⟪u,v⟫_ℝ := by
    rw [hQ,← hdiag I (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD),hi1u]
  change J (A.comp (I)) = Q (A+ContinuousLinearMap.adjoint A)
  rw [hJ,hQ]
  simp only [ContinuousLinearMap.comp_apply,hi2u,hi2v,ContinuousLinearMap.add_apply,inner_add_left,
    ContinuousLinearMap.adjoint_inner_left]
  rw [hdiag A hA,hdiagSwap A hA]


lemma nativeW_pairing_zero
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A)
    : nativeWSecondPairing hO hD F G x (ContinuousLinearMap.adjoint A) = nativeWSecondPairing hO hD F G x A := by
  let u := F x
  let v := G x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let v1 := coreWeightOperator hO hD (besselWeight 1) G x
  let u2 := coreWeightOperator hO hD (besselWeight 2) F x
  let v2 := coreWeightOperator hO hD (besselWeight 2) G x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let I := inverseDegreeMultiplier hO hD
  let Id := ContinuousLinearMap.id ℝ SphereL2
  have hu1 : (u,u1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) F x
  have hv1 : (v,v1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) G x
  have hu12 : (u1,u2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) F x,coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x
  have hv12 : (v1,v2) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) G x,coreWeightOperator hO hD (besselWeight 2) G x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD G x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) G) x
  have huh : (u,uh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x
  have hvh : (v,vh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x
  have hub : (uh,u1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hu1 k,huh k,smul_smul,← besselWeight_add]
    norm_num
  have hvb : (vh,v1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hv1 k,hvh k,smul_smul,← besselWeight_add]
    norm_num
  have hi2u : I u2 = u1 := inverseDegreeMultiplier_of_besselGraph hO hD u1 u2 hu12
  have hi2v : I v2 = v1 := inverseDegreeMultiplier_of_besselGraph hO hD v1 v2 hv12
  have hi1u : I u1 = u := inverseDegreeMultiplier_of_besselGraph hO hD u u1 hu1
  have hi1v : I v1 = v := inverseDegreeMultiplier_of_besselGraph hO hD v v1 hv1
  let J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ SphereL2 u2) +
      (innerSL ℝ u).comp (ContinuousLinearMap.apply ℝ SphereL2 v2)
  let Q : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ vh).comp (ContinuousLinearMap.apply ℝ SphereL2 uh)
  have hJ (A : SphereL2 →L[ℝ] SphereL2) : J A = ⟪A u2,v⟫_ℝ+⟪u,A v2⟫_ℝ := by
    change ⟪v,A u2⟫_ℝ+⟪u,A v2⟫_ℝ = _
    rw [real_inner_comm (A u2) v]
  have hQ (A : SphereL2 →L[ℝ] SphereL2) : Q A = ⟪A uh,vh⟫_ℝ := by
    change ⟪vh,A uh⟫_ℝ = _
    rw [real_inner_comm (A uh) vh]
  have hdiag (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪A u1,v⟫_ℝ = ⟪A uh,vh⟫_ℝ :=
    spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ)) (A uh) (A u1) v vh (hA _ uh u1 hub) hvh
  have hdiagSwap (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪u,A v1⟫_ℝ = ⟪uh,A vh⟫_ℝ := by
    have ht := spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ))
      (A vh) (A v1) u uh (hA _ vh v1 hvb) huh
    simpa only [real_inner_comm] using ht
  have hQ_I : Q I = ⟪u,v⟫_ℝ := by
    rw [hQ,← hdiag I (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD),hi1u]
  have hJadjDiff (A B : SphereL2 →L[ℝ] SphereL2)
      (hAB : ⟪A u2,v⟫_ℝ = ⟪u,B v2⟫_ℝ) (hBA : ⟪A v2,u⟫_ℝ = ⟪v,B u2⟫_ℝ) :
      J (A-B) = 0 := by
    rw [hJ]
    simp only [ContinuousLinearMap.sub_apply,inner_sub_left,inner_sub_right]
    have ht := hBA
    rw [real_inner_comm u (A v2),real_inner_comm (B u2) v] at ht
    rw [hAB,ht]
    ring
  change J (ContinuousLinearMap.adjoint A) = J A
  have hAB (F G : smoothCompactFiniteSphereCore hO hD) :
      ⟪ContinuousLinearMap.adjoint A (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ =
        ⟪F x,A (coreWeightOperator hO hD (besselWeight 2) G x)⟫_ℝ := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact spectralGraph_inner_symm hO hD (besselWeight 2) (F x)
      (coreWeightOperator hO hD (besselWeight 2) F x) (A (G x))
      (A (coreWeightOperator hO hD (besselWeight 2) G x))
      (coreWeightOperator_graph hO hD (besselWeight 2) F x)
      (hA _ _ _ (coreWeightOperator_graph hO hD (besselWeight 2) G x))
  have ht := hJadjDiff (ContinuousLinearMap.adjoint A) A (hAB F G) (hAB G F)
  rw [map_sub] at ht
  linarith

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
