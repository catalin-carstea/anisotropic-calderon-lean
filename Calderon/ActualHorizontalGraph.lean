import Calderon.ActualHorizontalGeometry

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualHorizontalNormBridge
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  SmoothSphereFields SmoothAngularApplication SmoothSphereRotationProjection
  SmoothSphereRotationBounds SmoothMovingFrameFields AmbientReferenceCovariantCore
  SmoothAmbientAngularCasimir
  MovingFrameConnection SmoothMetricFrame MetricOperator ConformalDepth RadiusProfile
  ReferenceDensityBounds ActualBalancedFirstPrincipalError ActualSupportLocalSecondForm
  SectionFiveErrorForms

lemma norm_harmonic_coordinates_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (C : ℝ) (hC : 0 ≤ C) (u v : SphereL2)
    (hcoord : ∀ k, ‖sphereHarmonicCoordinate hO hD k u‖ ≤
      C * ‖sphereHarmonicCoordinate hO hD k v‖) : ‖u‖ ≤ C * ‖v‖ := by
  have h := lp.norm_mono (p := 2) (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (x := sphereHarmonicDecomposition hO hD u)
    (y := C • sphereHarmonicDecomposition hO hD v) (fun k => by
      simpa only [lp.coeFn_smul,Pi.smul_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg hC,sphereHarmonicCoordinate_apply] using hcoord k)
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC,
    LinearIsometryEquiv.norm_map] using h

lemma norm_harmonic_rotation_le_two (k : ℕ) (a b : Fin 3)
    (u : harmonicSphereSubspace k) :
    ‖harmonicSphereRotation k a b u‖ ≤ 2 * (1+(k:ℝ)) * ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hf : 2*(k:ℝ)*((k:ℝ)+1) ≤ 4*(1+(k:ℝ))^2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  calc
    _ ≤ (2*(k:ℝ)*((k:ℝ)+1))*‖u‖^2 := norm_harmonicSphereRotation_sq_le k a b u
    _ ≤ (4*(1+(k:ℝ))^2)*‖u‖^2 :=
      mul_le_mul_of_nonneg_right hf (sq_nonneg _)
    _ = _ := by ring

/-- Degree-preserving rotations lose exactly one angular derivative on their true graph domain. -/
theorem norm_rotation_bessel_output_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (a b : Fin 3) (u higher r output : SphereL2)
    (hhigher : (u,higher) ∈ sphereBesselGraph hO hD (s+1))
    (hrotation : ∀ k, sphereHarmonicCoordinate hO hD k r =
      harmonicSphereRotation k a b (sphereHarmonicCoordinate hO hD k u))
    (houtput : (r,output) ∈ sphereBesselGraph hO hD s) :
    ‖output‖ ≤ 2 * ‖higher‖ := by
  apply norm_harmonic_coordinates_le hO hD 2 (by norm_num)
  intro k
  rw [houtput k,hrotation k,hhigher k]
  simp only [norm_smul,Real.norm_eq_abs,
    abs_of_pos (besselWeight_pos s k),abs_of_pos (besselWeight_pos (s+1) k)]
  calc
    _ ≤ besselWeight s k * (2*(1+(k:ℝ))*
        ‖sphereHarmonicCoordinate hO hD k u‖) :=
      mul_le_mul_of_nonneg_left (norm_harmonic_rotation_le_two k a b _) (besselWeight_pos s k).le
    _ = _ := by rw [besselWeight_add]; simp only [besselWeight,Real.rpow_one]; ring

def ambientRotationField (a b : Fin 3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  ambientSphereL2 (ambientAngularRotation a b G) (contDiff_ambientAngularRotation a b G hG)

def ambientHalfRotationField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a b : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  ambientBesselField hO hD (1/2 : ℝ) (by norm_num)
    (ambientAngularRotation a b G) (contDiff_ambientAngularRotation a b G hG)

lemma norm_ambient_rotation_le_one
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a b : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ‖ambientRotationField a b G hG x‖ ≤
      2 * ‖ambientBesselField hO hD 1 (by norm_num) G hG x‖ := by
  apply norm_rotation_bessel_output_le hO hD 0 a b (ambientSphereL2 G hG x)
    (ambientBesselField hO hD 1 (by norm_num) G hG x)
    (ambientRotationField a b G hG x)
  · simpa only [zero_add] using ambientBesselField_graph hO hD 1 (by norm_num) G hG x
  · exact fun k => sphereHarmonicCoordinate_ambientAngularRotation hO hD k a b G hG x
  · intro k
    simp only [besselWeight_zero_order,one_smul]

lemma norm_ambient_half_rotation_le_threehalf
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a b : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ‖ambientHalfRotationField hO hD a b G hG x‖ ≤
      2 * ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ := by
  apply norm_rotation_bessel_output_le hO hD (1/2 : ℝ) a b (ambientSphereL2 G hG x)
    (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x)
    (ambientRotationField a b G hG x)
  · convert ambientBesselField_graph hO hD (3/2 : ℝ) (by norm_num) G hG x using 1 <;> norm_num
  · exact fun k => sphereHarmonicCoordinate_ambientAngularRotation hO hD k a b G hG x
  · exact ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num)
      (ambientAngularRotation a b G) (contDiff_ambientAngularRotation a b G hG) x

/-- Horizontal differentiation in the actual Gram sphere trivialization. -/
def referenceHorizontalField (g : MatrixField) (L lam : ℝ) (U : R3 → SphereL2)
    (rotations : Fin 3 → Fin 3 → R3 → SphereL2) (x X : R3) : SphereL2 :=
  fderiv ℝ U x X + (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
    referenceFrameConnectionCoefficient g L lam x X a b • rotations a b x

def referenceHorizontalZero (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) : SphereL2 :=
  referenceHorizontalField g L lam (ambientSphereL2 G hG) (fun a b => ambientRotationField a b G hG) x X

def referenceHorizontalHalf (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (x X : R3) : SphereL2 :=
  referenceHorizontalField g L lam
    (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG)
    (fun a b => ambientHalfRotationField hO hD a b G hG) x X

lemma referenceFrameConnectionCoefficient_add (g : MatrixField) (L lam : ℝ)
    (x X Y : R3) (a b : Fin 3) :
    referenceFrameConnectionCoefficient g L lam x (X+Y) a b =
      referenceFrameConnectionCoefficient g L lam x X a b +
        referenceFrameConnectionCoefficient g L lam x Y a b := by
  simp only [referenceFrameConnectionCoefficient,frameConnectionCoefficient,
    covariantFrameDerivative,map_add,ContinuousLinearMap.add_apply,inner_add_left]
  ring

lemma referenceFrameConnectionCoefficient_smul (g : MatrixField) (L lam : ℝ)
    (x X : R3) (c : ℝ) (a b : Fin 3) :
    referenceFrameConnectionCoefficient g L lam x (c • X) a b =
      c * referenceFrameConnectionCoefficient g L lam x X a b := by
  simp only [referenceFrameConnectionCoefficient,frameConnectionCoefficient,
    covariantFrameDerivative,map_smul,ContinuousLinearMap.smul_apply,map_add,
    inner_add_left,real_inner_smul_left,mul_add]

def referenceHorizontalLinear (g : MatrixField) (L lam : ℝ) (U : R3 → SphereL2)
    (rotations : Fin 3 → Fin 3 → R3 → SphereL2) (x : R3) : R3 →ₗ[ℝ] SphereL2 where
  toFun := referenceHorizontalField g L lam U rotations x
  map_add' := by
    intro X Y
    simp only [referenceHorizontalField,map_add,referenceFrameConnectionCoefficient_add,
      add_smul,Finset.sum_add_distrib,smul_add]
    abel
  map_smul' := by
    intro c X
    change referenceHorizontalField g L lam U rotations x (c • X) =
      c • referenceHorizontalField g L lam U rotations x X
    simp only [referenceHorizontalField,map_smul,referenceFrameConnectionCoefficient_smul,
      smul_add,Finset.smul_sum,smul_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    ring

lemma referenceHorizontalField_sum (g : MatrixField) (L lam : ℝ) (U : R3 → SphereL2)
    (rotations : Fin 3 → Fin 3 → R3 → SphereL2) (x : R3)
    (c : Fin 3 → ℝ) (X : Fin 3 → R3) :
    referenceHorizontalField g L lam U rotations x (∑ i, c i • X i) =
      ∑ i, c i • referenceHorizontalField g L lam U rotations x (X i) := by
  change (referenceHorizontalLinear g L lam U rotations x) (∑ i, c i • X i) =
    ∑ i, c i • (referenceHorizontalLinear g L lam U rotations x) (X i)
  simp only [map_sum,map_smul]

/-- This is the genuine physical horizontal lift, not a new abstract connection. -/
lemma referenceHorizontalZero_eq_native (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ambientSphereL2
      (ambientFrameHorizontal (fun y => referenceFrameConnectionCoefficient g L lam y (X y)) X G)
      (contDiff_ambientFrameHorizontal _
        (fun a b => contDiff_referenceFrameConnectionCoefficient_field g hg L lam X hX a b)
        X hX G hG) x = referenceHorizontalZero g L lam G hG x (X x) := by
  exact ambientSphereL2_frameHorizontal _
    (fun a b => contDiff_referenceFrameConnectionCoefficient_field g hg L lam X hX a b)
    (fun y a b => referenceFrameConnectionCoefficient_skew g hg L lam y (X y) a b)
    X hX G hG x

/-- Half-order horizontal derivatives occupy exactly the source Bessel graph. -/
lemma referenceHorizontalHalf_graph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (x X : R3) :
    (referenceHorizontalZero g L lam G hG x X,
      referenceHorizontalHalf hO hD g L lam G hG x X) ∈
      sphereBesselGraph hO hD (1/2 : ℝ) := by
  have hd := directionalDeriv_besselGraph hO hD (1/2 : ℝ) X
    (ambientSphereL2 G hG) (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG)
    (contDiff_ambientSphereL2 G hG)
    (contDiff_ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG)
    (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) G hG) x
  intro k
  dsimp only [referenceHorizontalZero,referenceHorizontalHalf,referenceHorizontalField]
  simp only [map_add,map_smul,map_sum]
  rw [show sphereHarmonicCoordinate hO hD k
      (fderiv ℝ (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x X) =
      besselWeight (1/2 : ℝ) k • sphereHarmonicCoordinate hO hD k
        (fderiv ℝ (ambientSphereL2 G hG) x X) from hd k]
  simp_rw [show ∀ a b, sphereHarmonicCoordinate hO hD k
      (ambientHalfRotationField hO hD a b G hG x) = besselWeight (1/2 : ℝ) k •
      sphereHarmonicCoordinate hO hD k (ambientRotationField a b G hG x) from
    fun a b => ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num)
      (ambientAngularRotation a b G) (contDiff_ambientAngularRotation a b G hG) x k]
  simp only [smul_add,Finset.smul_sum,smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  ring

lemma referenceHorizontalHalf_eq_native
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ambientBesselField hO hD (1/2 : ℝ) (by norm_num)
      (ambientFrameHorizontal (fun y => referenceFrameConnectionCoefficient g L lam y (X y)) X G)
      (contDiff_ambientFrameHorizontal _
        (fun a b => contDiff_referenceFrameConnectionCoefficient_field g hg L lam X hX a b)
        X hX G hG) x = referenceHorizontalHalf hO hD g L lam G hG x (X x) := by
  have hn := ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num)
    (ambientFrameHorizontal (fun y => referenceFrameConnectionCoefficient g L lam y (X y)) X G)
    (contDiff_ambientFrameHorizontal _
      (fun a b => contDiff_referenceFrameConnectionCoefficient_field g hg L lam X hX a b)
      X hX G hG) x
  rw [referenceHorizontalZero_eq_native g hg L lam X hX G hG x] at hn
  exact spectralGraph_output_unique hO hD (besselWeight (1/2 : ℝ)) _ _ _ hn
    (referenceHorizontalHalf_graph hO hD g L lam G hG x (X x))

lemma norm_half_rotation_combination_le (c : Fin 3 → Fin 3 → ℝ)
    (r : Fin 3 → Fin 3 → SphereL2) (u : SphereL2) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ a b, |c a b| ≤ M) (hr : ∀ a b, ‖r a b‖ ≤ 2*‖u‖) :
    ‖(1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, c a b • r a b‖ ≤ 9*M*‖u‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  calc
    _ ≤ (1/2 : ℝ) * ∑ a : Fin 3, ∑ b : Fin 3, ‖c a b • r a b‖ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ (1/2 : ℝ) * ∑ _a : Fin 3, ∑ _b : Fin 3, M*(2*‖u‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hc a b) (hr a b) (norm_nonneg _) hM
    _ = _ := by simp; ring

lemma norm_referenceHorizontalZero_correction_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (x X : R3) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ a b, |referenceFrameConnectionCoefficient g L lam x X a b| ≤ M) :
    ‖referenceHorizontalZero g L lam G hG x X - fderiv ℝ (ambientSphereL2 G hG) x X‖ ≤
      9*M*‖ambientBesselField hO hD 1 (by norm_num) G hG x‖ := by
  unfold referenceHorizontalZero referenceHorizontalField
  rw [add_sub_cancel_left]
  exact norm_half_rotation_combination_le _ _ _ M hM hc
    (fun a b => norm_ambient_rotation_le_one hO hD a b G hG x)

lemma norm_referenceHorizontalHalf_correction_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (x X : R3) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ a b, |referenceFrameConnectionCoefficient g L lam x X a b| ≤ M) :
    ‖referenceHorizontalHalf hO hD g L lam G hG x X -
        fderiv ℝ (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x X‖ ≤
      9*M*‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ := by
  unfold referenceHorizontalHalf referenceHorizontalField
  rw [add_sub_cancel_left]
  exact norm_half_rotation_combination_le _ _ _ M hM hc
    (fun a b => norm_ambient_half_rotation_le_threehalf hO hD a b G hG x)

end OAI.AnisotropicCalderon.ActualHorizontalNormBridge
