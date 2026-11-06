import Calderon.CoordinateHarmonicProductDecomposition
import Calderon.NativeHarmonicPolynomialHalfProjection
import Calderon.NativeHalfSmoothMultiplier

set_option autoImplicit false
noncomputable section
open MvPolynomial Set MeasureTheory
open scoped ENNReal ContDiff Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic AngularPolynomial HarmonicCoordinateCompatibility
  NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion
  NativeFullSharpHalfTrace NativeHalfSmoothMultiplier

lemma harmonicHalfProjection_coordinate_defect
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : ℕ) (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) :
    harmonicFirstOrderLiftCompletion hF
        (nativeHalfTraceL hF hO hD τ0 (nativePolynomialFirstOrderL (X i*p))) -
      nativePolynomialFirstOrderL (X i*p) =
    nativePolynomialFirstOrderL ((1-radiusSq)*(C ((2*(k:ℝ)+1)⁻¹)*pderiv i p)) := by
  let H := coordinateHarmonicRaising k i p
  let q := C ((2*(k:ℝ)+1)⁻¹)*pderiv i p
  let I := nativePolynomialFirstOrderL
  let T := nativeHalfTraceL hF hO hD τ0
  let P := harmonicFirstOrderLiftCompletion hF
  have hH : H ∈ harmonicHomogeneous (k+1) :=
    coordinateHarmonicRaising_mem_all_degrees k i p hp
  have hq : q ∈ harmonicHomogeneous (k-1) := by
    simpa only [MvPolynomial.smul_eq_C_mul] using
      (harmonicHomogeneous (k-1)).smul_mem ((2*(k:ℝ)+1)⁻¹)
        (pderiv_harmonicHomogeneous_pred k i p hp)
  have hI : I H + I q - I (X i*p) = I ((1-radiusSq)*q) := by
    simpa only [map_sub,map_add] using
      congrArg I (coordinateHarmonicProduct_defect_polynomial k i p)
  have hz : I ((1-radiusSq)*q) ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    nativePolynomialFirstOrderL_radialFactor_mem_zero q
  have hTz : T (I ((1-radiusSq)*q)) = 0 :=
    nativeHalfTraceL_zeroDirichlet hF hO hD τ0 ⟨I ((1-radiusSq)*q),hz⟩
  have hT : T (I H) + T (I q) - T (I (X i*p)) = 0 := by
    have h := congrArg T hI
    simpa only [map_sub,map_add,hTz] using h
  have hP : P (T (I (X i*p))) = I H + I q := by
    have h := congrArg P (sub_eq_zero.mp hT).symm
    rw [map_add] at h
    have hPH : P (T (I H)) = I H :=
      harmonicHalfProjection_nativePolynomial hF hO hD τ0 (k+1) H hH
    have hPq : P (T (I q)) = I q :=
      harmonicHalfProjection_nativePolynomial hF hO hD τ0 (k-1) q hq
    exact h.trans (congrArg₂ (fun x y : BallH1 => x+y) hPH hPq)
  change P (T (I (X i*p))) - I (X i*p) = I ((1-radiusSq)*q)
  rw [hP]
  exact hI

lemma contDiffSMulL_coordinate_nativePolynomial
    (i : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(smoothPolynomialData (X i)).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (smoothPolynomialData (X i)).1 x‖ ≤ M)
    (p : MvPolynomial (Fin 3) ℝ) :
    TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) (smoothPolynomialData (X i)).1 (smoothPolynomialData (X i)).2 hM hm hg
      (nativePolynomialFirstOrderL p) = nativePolynomialFirstOrderL (X i*p) := by
  rw [nativePolynomialFirstOrderL_apply,contDiffSMulL_smoothSobolev,
    nativePolynomialFirstOrderL_apply]
  congr 1
  apply Subtype.ext
  funext x
  exact (map_mul (eval (polynomialCoordinateMap x)) (X i) p).symm

lemma harmonicFirstOrderLift_coordinate_defect_single_mem_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(smoothPolynomialData (X i)).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (smoothPolynomialData (X i)).1 x‖ ≤ M)
    (k : ℕ) (u : harmonicSphereSubspace k) :
    harmonicFirstOrderLiftCompletion hF
      (nativeHalfSmoothMulL hF hO hD τ0 (smoothPolynomialData (X i)) hM hm hg
        (sphereSobolevSingleL (1/2:ℝ) k u)) -
    TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) (smoothPolynomialData (X i)).1 (smoothPolynomialData (X i)).2 hM hm hg
      (harmonicFirstOrderLiftCompletion hF (sphereSobolevSingleL (1/2:ℝ) k u)) ∈
    TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let p := harmonicPolynomialRepresentativeL hF k u
  have hp : p ∈ harmonicHomogeneous k := harmonicPolynomialRepresentative_mem hF k u
  have hsingle : harmonicFirstOrderLiftCompletion hF (sphereSobolevSingleL (1/2:ℝ) k u) =
      nativePolynomialFirstOrderL p := by
    rw [harmonicFirstOrderLiftCompletion_single hF hO,nativePolynomialFirstOrderL_apply]
  change harmonicFirstOrderLiftCompletion hF
      (nativeHalfTraceL hF hO hD τ0
        (TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) (smoothPolynomialData (X i)).1 (smoothPolynomialData (X i)).2 hM hm hg
          (harmonicFirstOrderLiftCompletion hF (sphereSobolevSingleL (1/2:ℝ) k u)))) - _ ∈ _
  simp only [hsingle,contDiffSMulL_coordinate_nativePolynomial]
  rw [harmonicHalfProjection_coordinate_defect hF hO hD τ0 k i p hp]
  exact nativePolynomialFirstOrderL_radialFactor_mem_zero _

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.harmonicHalfProjection_coordinate_defect
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffSMulL_coordinate_nativePolynomial
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.harmonicFirstOrderLift_coordinate_defect_single_mem_zero
