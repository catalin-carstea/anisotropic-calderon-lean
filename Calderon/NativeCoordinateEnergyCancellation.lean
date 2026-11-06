import Calderon.NativeSmoothCoordinateDerivative
import Calderon.NativeSmoothMultiplicationTrace
import Calderon.NativeCoefficientWeakEnergy

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

/-! Upfront expansion: EXPANSION-native-coordinate-energy-cancellation-joint-v001.md. -/

theorem realBilinear_coordinate_product_cancel
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (U V' e : V) (t u v : ℝ) :
    B (t • U + u • e) V' - B U (t • V' + v • e) =
      u * B e V' - v * B U e := by
  simp only [map_add,map_smul,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem gradient_coordinate_projection (k : Fin 3) (x : R3) :
    gradient (fun y : R3 => y k) x = EuclideanSpace.single k 1 := by
  ext j
  rw [gradient_coordinate]
  change fderiv ℝ (EuclideanSpace.proj k : R3 →L[ℝ] ℝ) x
    (coordinateVector j) = (EuclideanSpace.single k 1) j
  rw [ContinuousLinearMap.fderiv]
  simp [coordinateVector,PiLp.single_apply,eq_comm]

def coordinateSmoothDatum (k : Fin 3) : SmoothData :=
  ⟨fun x : R3 => x k,(EuclideanSpace.proj k : R3 →L[ℝ] ℝ).contDiff⟩

theorem coordinate_product_jetField_ae
    (k : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coordinateSmoothDatum k).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coordinateSmoothDatum k).1 x‖ ≤ M)
    (u : BallH1) :
    TauCeti.PDE.jetField (TauCeti.W1p.contDiffSMulL
      (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
      (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => x k • TauCeti.PDE.jetField u x +
        TauCeti.W1p.value u x • ((0 : ℝ),EuclideanSpace.single k 1) := by
  rw [TauCeti.W1p.contDiffSMulL_apply]
  filter_upwards [TauCeti.W1p.value_contDiffSMul_ae (coordinateSmoothDatum k).2 hM hm hg u,
    TauCeti.W1p.gradient_contDiffSMul_ae (coordinateSmoothDatum k).2 hM hm hg u]
    with x hv hgrad
  rw [TauCeti.PDE.jetField_apply,hv,hgrad,TauCeti.PDE.jetField_apply]
  simp only [coordinateSmoothDatum,gradient_coordinate_projection,Prod.smul_mk,
    Prod.mk_add_mk,smul_eq_mul,mul_zero,add_zero]

theorem nativeEnergy_coordinate_product_difference_integral
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (k : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coordinateSmoothDatum k).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coordinateSmoothDatum k).1 x‖ ≤ M)
    (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b c
      (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg u) v -
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b c u
      (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg v) =
    ∫ x in ballOpens,
      TauCeti.W1p.value u x * TauCeti.PDE.energyIntegrand (a x) (b x) (c x)
        ((0 : ℝ),EuclideanSpace.single k 1) (TauCeti.PDE.jetField v x) -
      TauCeti.W1p.value v x * TauCeti.PDE.energyIntegrand (a x) (b x) (c x)
        (TauCeti.PDE.jetField u x) ((0 : ℝ),EuclideanSpace.single k 1) := by
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL
    (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg
  have hi1 := TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff (S u) v
  have hi2 := TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff u (S v)
  rw [TauCeti.PDE.energyFormH1_def,TauCeti.PDE.energyFormH1_def,← integral_sub hi1 hi2]
  apply integral_congr_ae
  filter_upwards [coordinate_product_jetField_ae k hM hm hg u,
    coordinate_product_jetField_ae k hM hm hg v] with x hu hv
  rw [hu,hv]
  exact realBilinear_coordinate_product_cancel
    (TauCeti.PDE.energyIntegrand (a x) (b x) (c x))
    (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x)
    ((0 : ℝ),EuclideanSpace.single k 1) (x k) (TauCeti.W1p.value u x) (TauCeti.W1p.value v x)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
