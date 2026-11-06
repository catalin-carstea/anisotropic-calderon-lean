import Calderon.ActualFiniteHarmonicModelShiftWeights
import Calderon.SectionFiveErrorForms

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity ActualFiniteHarmonicCore
  SpectralWeightedGraph BoundedAngularShift AngularShiftGraph PrincipalCommutator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeThirdShiftFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeThirdShiftFunction

lemma coreWeight_two_derivative_apply_eq_normalized_polynomial
    (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight 2) (coreDerivative hO hD hF i F) x =
      normalizedDerivative hF hO hD i
        (coreWeightOperator hO hD (besselWeight 3) F x -
          (2 : ℝ) • coreWeightOperator hO hD (besselWeight 2) F x +
            coreWeightOperator hO hD (besselWeight 1) F x) := by
  let W1 := coreWeightOperator hO hD (besselWeight 1)
  let W2 := coreWeightOperator hO hD (besselWeight 2)
  let W3 := coreWeightOperator hO hD (besselWeight 3)
  let D := coreDerivative hO hD hF i
  have h11 (G : smoothCompactFiniteSphereCore hO hD) : W1 (W1 G) = W2 G := by
    apply Subtype.ext
    funext y
    exact coreWeight_one_twice_apply hO hD G y
  have h12 (G : smoothCompactFiniteSphereCore hO hD) : W1 (W2 G) = W3 G := by
    apply Subtype.ext
    funext y
    apply (sphereHarmonicDecomposition hO hD).injective
    apply lp.ext
    funext k
    change sphereHarmonicCoordinate hO hD k
        (coreWeightOperator hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 2) G) y) =
      sphereHarmonicCoordinate hO hD k (coreWeightOperator hO hD (besselWeight 3) G y)
    rw [(coreWeightOperator_graph hO hD (besselWeight 1) (W2 G) y) k,
      (coreWeightOperator_graph hO hD (besselWeight 2) G y) k,
      (coreWeightOperator_graph hO hD (besselWeight 3) G y) k, smul_smul]
    have hb : besselWeight 3 k = besselWeight 1 k * besselWeight 2 k := by
      simpa only [show (1+2 : ℝ)=3 by norm_num] using
        SectionFiveErrorForms.besselWeight_add 1 2 k
    rw [hb]
  have hshift (G : smoothCompactFiniteSphereCore hO hD) : W1 (D G) = D (W1 G)-D G := by
    apply Subtype.ext
    funext y
    change W1 (D G) y = D (W1 G) y-D G y
    apply (sphereHarmonicDecomposition hO hD).injective
    apply lp.ext
    funext k
    change sphereHarmonicCoordinate hO hD k
        (coreWeightOperator hO hD (besselWeight 1) (coreDerivative hO hD hF i G) y) =
      sphereHarmonicCoordinate hO hD k
        (coreDerivative hO hD hF i (coreWeightOperator hO hD (besselWeight 1) G) y-
          coreDerivative hO hD hF i G y)
    rw [map_sub,
      (coreWeightOperator_graph hO hD (besselWeight 1) (coreDerivative hO hD hF i G) y) k,
      (coreDerivative_graph hO hD hF i G y) k,
      (coreDerivative_graph hO hD hF i (W1 G) y) k,
      (coreWeightOperator_graph hO hD (besselWeight 1) G y) (k+1), map_smul]
    simp only [besselWeight, Real.rpow_one, Nat.cast_add, Nat.cast_one]
    module
  have htwo : W2 (D F) = D (W2 F)-(2 : ℝ) • D (W1 F)+D F := by
    calc
      W2 (D F) = W1 (W1 (D F)) := (h11 (D F)).symm
      _ = W1 (D (W1 F)-D F) := congrArg W1 (hshift F)
      _ = W1 (D (W1 F))-W1 (D F) := map_sub W1 _ _
      _ = (D (W1 (W1 F))-D (W1 F))-(D (W1 F)-D F) := by
        rw [hshift (W1 F), hshift F]
      _ = D (W2 F)-(2 : ℝ) • D (W1 F)+D F := by
        rw [h11 F, two_smul]
        abel
  have hD2 : D (W2 F) x = normalizedDerivative hF hO hD i (W3 F x) := by
    change normalizedDerivative hF hO hD i (W1 (W2 F) x) = _
    rw [h12 F]
  have hD1 : D (W1 F) x = normalizedDerivative hF hO hD i (W2 F x) := by
    change normalizedDerivative hF hO hD i (W1 (W1 F) x) = _
    rw [h11 F]
  have he := congrArg (fun G : smoothCompactFiniteSphereCore hO hD => G x) htwo
  simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
    Pi.sub_apply, Pi.add_apply, Pi.smul_apply] at he
  calc
    _ = normalizedDerivative hF hO hD i (W3 F x) -
        (2 : ℝ) • normalizedDerivative hF hO hD i (W2 F x) +
          normalizedDerivative hF hO hD i (W1 F x) := by
      rw [hD2, hD1] at he
      exact he
    _ = _ := by dsimp only [W1, W2, W3]; simp only [map_add, map_sub, map_smul]

lemma coreWeight_two_derivative_apply_eq_normalized_third_weight
    (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight 2) (coreDerivative hO hD hF i F) x =
      ((normalizedDerivative hF hO hD i).comp
        ((ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD).comp
          (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD)))
        (coreWeightOperator hO hD (besselWeight 3) F x) := by
  let I := inverseDegreeMultiplier hO hD
  let Id := ContinuousLinearMap.id ℝ SphereL2
  have h23 : (coreWeightOperator hO hD (besselWeight 2) F x,
      coreWeightOperator hO hD (besselWeight 3) F x) ∈ sphereBesselGraph hO hD 1 := by
    intro k
    rw [(coreWeightOperator_graph hO hD (besselWeight 3) F x) k,
      (coreWeightOperator_graph hO hD (besselWeight 2) F x) k, smul_smul]
    have hb : besselWeight 3 k = besselWeight 1 k * besselWeight 2 k := by
      simpa only [show (1+2 : ℝ)=3 by norm_num] using
        SectionFiveErrorForms.besselWeight_add 1 2 k
    rw [hb]
  have h12 : (coreWeightOperator hO hD (besselWeight 1) F x,
      coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1 := by
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1)
      (coreWeightOperator hO hD (besselWeight 1) F) x
  have hi3 : I (coreWeightOperator hO hD (besselWeight 3) F x) =
      coreWeightOperator hO hD (besselWeight 2) F x :=
    inverseDegreeMultiplier_of_besselGraph hO hD _ _ h23
  have hi2 : I (coreWeightOperator hO hD (besselWeight 2) F x) =
      coreWeightOperator hO hD (besselWeight 1) F x :=
    inverseDegreeMultiplier_of_besselGraph hO hD _ _ h12
  have hComplementZero (u : SphereL2) : sphereHarmonicCoordinate hO hD 0 ((Id-I) u) = 0 := by
    simp only [Id, I, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub,
      inverseDegreeMultiplier_coordinate, inverseDegreeWeight, Nat.cast_zero,
      add_zero, inv_one, one_smul, sub_self]
  have hSquareZero (u : SphereL2) :
      sphereHarmonicCoordinate hO hD 0 (((Id-I).comp (Id-I)) u) = 0 := by
    exact hComplementZero ((Id-I) u)
  have hpoly : ((Id-I).comp (Id-I)) (coreWeightOperator hO hD (besselWeight 3) F x) =
      coreWeightOperator hO hD (besselWeight 3) F x -
        (2 : ℝ) • coreWeightOperator hO hD (besselWeight 2) F x +
          coreWeightOperator hO hD (besselWeight 1) F x := by
    dsimp only [Id]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, map_sub, hi3, hi2, two_smul]
    abel
  calc
    _ = normalizedDerivative hF hO hD i
      (coreWeightOperator hO hD (besselWeight 3) F x -
        (2 : ℝ) • coreWeightOperator hO hD (besselWeight 2) F x +
          coreWeightOperator hO hD (besselWeight 1) F x) :=
      coreWeight_two_derivative_apply_eq_normalized_polynomial hO hD hF i F x
    _ = normalizedDerivative hF hO hD i
      (((Id-I).comp (Id-I)) (coreWeightOperator hO hD (besselWeight 3) F x)) :=
      congrArg (normalizedDerivative hF hO hD i) hpoly.symm
    _ = _ := rfl

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
