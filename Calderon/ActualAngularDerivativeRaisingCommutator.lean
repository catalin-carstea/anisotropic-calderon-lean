import Calderon.ActualAngularPolynomialCommutator
import Calderon.ActualPhysicalPureAngular
import Calderon.ActualReferenceDDSpectralTransport

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualAngularDerivativeRaisingCommutator
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift BoundedSpectralMultiplier HarmonicDerivativeOperator
  SmoothSphereFields SmoothAngularApplication AmbientAngularShift AngularDerivativeBesselField
  ActualPhysicalPureAngular ActualAngularPolynomialCommutator ActualReferenceDDSpectralTransport

def derivativeRaisingFirstWeight (k : ℕ) : ℝ := 2*(k:ℝ)/(2*(k:ℝ)+1)
def derivativeRaisingSecondWeight (k : ℕ) : ℝ := 2*(k:ℝ)*(2*(k:ℝ)+3)/(2*(k:ℝ)+1)^2

lemma abs_derivativeRaisingFirstWeight_le_one (k : ℕ) :
    |derivativeRaisingFirstWeight k| ≤ 1 := by
  unfold derivativeRaisingFirstWeight
  have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hd : 0 < 2*(k:ℝ)+1 := by positivity
  rw [abs_of_nonneg (div_nonneg (by positivity) hd.le)]
  apply (div_le_iff₀ hd).mpr
  linarith
lemma abs_derivativeRaisingSecondWeight_le_two (k : ℕ) :
    |derivativeRaisingSecondWeight k| ≤ 2 := by
  unfold derivativeRaisingSecondWeight
  have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hd : 0 < (2*(k:ℝ)+1)^2 := by positivity
  rw [abs_of_nonneg (div_nonneg (by positivity) hd.le)]
  apply (div_le_iff₀ hd).mpr
  nlinarith [sq_nonneg (k:ℝ)]

def derivativeRaisingFirstMultiplier
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) : SphereL2 →L[ℝ] SphereL2 :=
  boundedSpectralMultiplier hO hD derivativeRaisingFirstWeight 1 (by norm_num)
    abs_derivativeRaisingFirstWeight_le_one

def derivativeRaisingSecondMultiplier
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) : SphereL2 →L[ℝ] SphereL2 :=
  boundedSpectralMultiplier hO hD derivativeRaisingSecondWeight 2 (by norm_num)
    abs_derivativeRaisingSecondWeight_le_two

def normalizedDerivativeRaisingCommutator
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
  (if i=j then (2:ℝ) • ContinuousLinearMap.id ℝ SphereL2 + inverseDegreeMultiplier hO hD else 0) +
    (derivativeRaisingFirstMultiplier hO hD).comp
      ((normalizedRaising hF hO hD j).comp (normalizedDerivative hF hO hD i)) -
    (derivativeRaisingSecondMultiplier hO hD).comp
      ((normalizedRaising hF hO hD i).comp (normalizedDerivative hF hO hD j))

lemma norm_normalizedDerivativeRaisingCommutator_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) : ‖normalizedDerivativeRaisingCommutator hF hO hD i j‖ ≤ 15 := by
  have hInv := ActualReferenceDDNormalizedCoefficient.norm_inverseDegreeMultiplier_le_one hO hD
  have hM1 : ‖derivativeRaisingFirstMultiplier hO hD‖ ≤ 1 :=
    norm_boundedSpectralMultiplier_le hO hD _ 1 (by norm_num) abs_derivativeRaisingFirstWeight_le_one
  have hM2 : ‖derivativeRaisingSecondMultiplier hO hD‖ ≤ 2 :=
    norm_boundedSpectralMultiplier_le hO hD _ 2 (by norm_num) abs_derivativeRaisingSecondWeight_le_two
  have hDiag : ‖(if i=j then (2:ℝ) • ContinuousLinearMap.id ℝ SphereL2 + inverseDegreeMultiplier hO hD else 0)‖ ≤ 3 := by
    by_cases h : i=j
    · simp only [h,if_pos]
      calc
        _ ≤ ‖(2:ℝ) • ContinuousLinearMap.id ℝ SphereL2‖ + ‖inverseDegreeMultiplier hO hD‖ := norm_add_le _ _
        _ ≤ 2*1+1 := by
          rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
          exact add_le_add (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by norm_num)) hInv
        _ = 3 := by norm_num
    · simp [h]
  have hRD (a c : Fin 3) : ‖(normalizedRaising hF hO hD a).comp (normalizedDerivative hF hO hD c)‖ ≤ 4 := by
    calc
      _ ≤ ‖normalizedRaising hF hO hD a‖*‖normalizedDerivative hF hO hD c‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 2*2 := mul_le_mul (norm_normalizedRaising_le hF hO hD a)
        (norm_normalizedDerivative_le hF hO hD c) (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hP1 : ‖(derivativeRaisingFirstMultiplier hO hD).comp
      ((normalizedRaising hF hO hD j).comp (normalizedDerivative hF hO hD i))‖ ≤ 4 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa using mul_le_mul hM1 (hRD j i) (norm_nonneg _) (by norm_num : (0:ℝ)≤1))
  have hP2 : ‖(derivativeRaisingSecondMultiplier hO hD).comp
      ((normalizedRaising hF hO hD i).comp (normalizedDerivative hF hO hD j))‖ ≤ 8 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by convert mul_le_mul hM2 (hRD i j) (norm_nonneg _) (by norm_num : (0:ℝ)≤2) using 1 <;> norm_num)
  unfold normalizedDerivativeRaisingCommutator
  exact (norm_sub_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add hDiag hP1)) hP2).trans (by norm_num))

lemma normalizedRaising_derivative_coordinate
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) (u : SphereL2) (m : ℕ) :
    sphereHarmonicCoordinate hO hD (m+1)
      (normalizedRaising hF hO hD j (normalizedDerivative hF hO hD i u)) =
    (inverseDegreeWeight m*inverseDegreeWeight (m+1)) •
      harmonicDerivativeAdjoint hF m j (harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) u)) := by
  have hR := (normalizedRaisingOutput_graph hF hO hD j (normalizedDerivative hF hO hD i u)).2 m
  have hDer : sphereHarmonicCoordinate hO hD m (normalizedDerivative hF hO hD i u) =
      harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) (inverseDegreeMultiplier hO hD u)) :=
    normalizedDerivativeOutput_graph hF hO hD i u m
  change sphereHarmonicCoordinate hO hD (m+1)
      (normalizedRaisingOutput hF hO hD j (normalizedDerivative hF hO hD i u)) = _
  rw [hR,inverseDegreeMultiplier_coordinate,hDer,inverseDegreeMultiplier_coordinate]
  simp only [map_smul,smul_smul]

theorem ambientDerivativeRaising_commutator_eq_normalized
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    normalizedDerivative hF hO hD i (ambientRaisingBesselField hF hO hD j G hG x) -
      normalizedRaising hF hO hD j (ambientDerivativeBesselField hF hO hD i G hG x) =
    normalizedDerivativeRaisingCommutator hF hO hD i j
      (ambientBesselField hO hD 1 (by norm_num) G hG x) := by
  have hLow := normalizedDerivative_graph hF hO hD i
    (ambientRaisingField hF hO hD j G hG x) (ambientRaisingBesselField hF hO hD j G hG x)
    (ambientRaisingBesselField_graph hF hO hD j G hG x)
  have hRaise := normalizedRaising_graph hF hO hD j
    (ambientDerivativeField hF hO hD i G hG x) (ambientDerivativeBesselField hF hO hD i G hG x)
    (ambientDerivativeBesselField_graph hF hO hD i G hG x)
  have hM1 (z : SphereL2) (k : ℕ) : sphereHarmonicCoordinate hO hD k (derivativeRaisingFirstMultiplier hO hD z) =
      derivativeRaisingFirstWeight k • sphereHarmonicCoordinate hO hD k z :=
    boundedSpectralMultiplier_mem hO hD _ 1 (by norm_num) abs_derivativeRaisingFirstWeight_le_one z k
  have hM2 (z : SphereL2) (k : ℕ) : sphereHarmonicCoordinate hO hD k (derivativeRaisingSecondMultiplier hO hD z) =
      derivativeRaisingSecondWeight k • sphereHarmonicCoordinate hO hD k z :=
    boundedSpectralMultiplier_mem hO hD _ 2 (by norm_num) abs_derivativeRaisingSecondWeight_le_two z k
  have hB (k : ℕ) :
      sphereHarmonicCoordinate hO hD k (ambientBesselField hO hD 1 (by norm_num) G hG x) =
        besselWeight 1 k • sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG x) :=
    (ambientBesselField_graph hO hD 1 (by norm_num) G hG x) k
  have hz (a c : Fin 3) (z : SphereL2) : sphereHarmonicCoordinate hO hD 0
      (normalizedRaising hF hO hD a (normalizedDerivative hF hO hD c z)) = 0 :=
    (normalizedRaisingOutput_graph hF hO hD a (normalizedDerivative hF hO hD c z)).1
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
      (normalizedDerivative hF hO hD i (ambientRaisingBesselField hF hO hD j G hG x) -
        normalizedRaising hF hO hD j (ambientDerivativeBesselField hF hO hD i G hG x)) =
    sphereHarmonicCoordinate hO hD k (normalizedDerivativeRaisingCommutator hF hO hD i j
      (ambientBesselField hO hD 1 (by norm_num) G hG x))
  cases k with
  | zero =>
    rw [map_sub,hLow 0,hRaise.1,sub_zero,(ambientRaisingField_graph hF hO hD j G hG x).2 0,
      harmonicDerivativeAdjoint_zero_commutator]
    by_cases hij : i=j
    · simp only [hij,ite_true,eq_self_iff_true,normalizedDerivativeRaisingCommutator,ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply,map_add,map_sub,map_smul,hM1,hM2,hz,
        inverseDegreeMultiplier_coordinate,hB,smul_zero,sub_zero,add_zero,
        inverseDegreeWeight,besselWeight,Real.rpow_one,Nat.cast_zero,zero_add,inv_one,one_smul]
      module
    · simp only [hij,ite_false,normalizedDerivativeRaisingCommutator,ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.zero_apply,
        map_add,map_sub,hM1,hM2,hz,smul_zero,zero_add,sub_zero]
  | succ m =>
    rw [map_sub,hLow (m+1),hRaise.2 m,
      (ambientRaisingField_graph hF hO hD j G hG x).2 (m+1),
      ambientDerivativeField_graph hF hO hD i G hG x m,harmonicDerivativeAdjoint_commutator]
    have hDiag :
        sphereHarmonicCoordinate hO hD (m+1)
          ((if i=j then (2:ℝ) • ContinuousLinearMap.id ℝ SphereL2 + inverseDegreeMultiplier hO hD else 0)
            (ambientBesselField hO hD 1 (by norm_num) G hG x)) =
        if i=j then (2*(m:ℝ)+5) • sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG x) else 0 := by
      have hc : 2*besselWeight 1 (m+1)+inverseDegreeWeight (m+1)*besselWeight 1 (m+1) = 2*(m:ℝ)+5 := by
        simp only [besselWeight,Real.rpow_one,inverseDegreeWeight]
        push_cast
        field_simp
        ring
      by_cases hij : i=j
      · simp only [hij,ite_true,eq_self_iff_true,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.id_apply,map_add,map_smul,inverseDegreeMultiplier_coordinate,
          hB,smul_smul,← add_smul,hc]
      · simp [hij]
    have hFirst : derivativeRaisingFirstWeight (m+1)*
        (inverseDegreeWeight m*(inverseDegreeWeight (m+1)*besselWeight 1 (m+1))) = 2/(2*(m:ℝ)+3) := by
      simp only [derivativeRaisingFirstWeight,inverseDegreeWeight,besselWeight,Real.rpow_one]
      push_cast
      field_simp
      ring
    have hSecond : derivativeRaisingSecondWeight (m+1)*
        (inverseDegreeWeight m*(inverseDegreeWeight (m+1)*besselWeight 1 (m+1))) =
        2*(2*(m:ℝ)+5)/(2*(m:ℝ)+3)^2 := by
      simp only [derivativeRaisingSecondWeight,inverseDegreeWeight,besselWeight,Real.rpow_one]
      push_cast
      field_simp
      ring
    simp only [normalizedDerivativeRaisingCommutator,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,map_add,map_sub,hDiag,hM1,hM2,
      normalizedRaising_derivative_coordinate,hB,map_smul,smul_smul,mul_assoc,hFirst,hSecond]
    by_cases hij : i=j <;> simp [hij]

theorem norm_ambientDerivativeRaising_commutator_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ‖normalizedDerivative hF hO hD i (ambientRaisingBesselField hF hO hD j G hG x) -
      normalizedRaising hF hO hD j (ambientDerivativeBesselField hF hO hD i G hG x)‖ ≤
      15*‖ambientBesselField hO hD 1 (by norm_num) G hG x‖ := by
  rw [ambientDerivativeRaising_commutator_eq_normalized]
  exact (normalizedDerivativeRaisingCommutator hF hO hD i j).le_of_opNorm_le
    (norm_normalizedDerivativeRaisingCommutator_le hF hO hD i j) _

end OAI.AnisotropicCalderon.ActualAngularDerivativeRaisingCommutator
