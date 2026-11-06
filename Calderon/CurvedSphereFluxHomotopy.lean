import Calderon.ActualBallDivergenceFlux
import Calderon.CoordinatePiolaCovariance
import Calderon.FixedSurfaceFluxIntegration
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.CurvedSurfaceTransfer
open EnergyBridge ConnectionError SphereHarmonic RadialTestIntegration

/-- Oriented Piola flux. The measure here is physical unit-sphere surface
measure, not its probability normalization. -/
def piolaSphereFlux (H : ℝ × R3 → R3) (Z : R3 → R3) (t : ℝ) : ℝ :=
  ∫ theta : UnitSphere, ⟪theta.val,
    signedPiolaFlux (fun x => H (t,x)) Z theta.val⟫_ℝ ∂surfaceMeasure

end OAI.AnisotropicCalderon.CurvedSurfaceTransfer

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.CurvedSurfaceTransfer
open EnergyBridge ConnectionError SphereHarmonic RadialTestIntegration

local notation "cv" => NormalCoordinatesFrame.coordinateVector

/-! ### H1: coordinate-form unit-ball Gauss theorem -/

theorem clm_apply_eq_sum (L : R3 →L[ℝ] ℝ) (w : R3) :
    L w = ∑ b : Fin 3, w b * L (cv b) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w]
  simp [map_sum, NormalCoordinatesFrame.coordinateVector]

theorem fderiv_component {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (V : D → R3) (x w : D) (i : Fin 3) (hV : DifferentiableAt ℝ V x) :
    fderiv ℝ (fun y => (V y) i) x w = (fderiv ℝ V x w) i := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hV.hasFDerivAt
  change fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i) ∘ V) x w = _
  rw [h.fderiv]
  rfl

theorem radialDivergence_basisFun (V : R3 → R3) (x : R3) (hV : DifferentiableAt ℝ V x) :
    radialDivergence (EuclideanSpace.basisFun (Fin 3) ℝ) V x =
      coordinateFluxDivergence V x := by
  unfold radialDivergence coordinateFluxDivergence
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_component V x _ i hV]
  simp [NormalCoordinatesFrame.coordinateVector, EuclideanSpace.inner_single_left]

theorem integral_ball_coordinateFluxDivergence (V : R3 → R3) (hV : ContDiff ℝ ∞ V) :
    (∫ x in ball (0 : R3) 1, coordinateFluxDivergence V x) =
      ∫ θ : UnitSphere, ⟪θ.val, V θ.val⟫_ℝ ∂surfaceMeasure := by
  have hV1 : ContDiff ℝ 1 V := by simpa using contDiff_infty.1 hV 1
  rw [← integral_unitBall_radialDivergence_eq_surfaceFlux
    (EuclideanSpace.basisFun (Fin 3) ℝ) V hV1]
  refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
  exact (radialDivergence_basisFun V x (hV.differentiable (by simp) x)).symm

theorem coordinateFluxDivergence_eq_sum (V : R3 → R3) (hV : Differentiable ℝ V) (x : R3) :
    coordinateFluxDivergence V x = ∑ i, coordinateJacobianMatrix V x i i := by
  unfold coordinateFluxDivergence coordinateJacobianMatrix
  exact Finset.sum_congr rfl fun i _ => fderiv_component V x _ i (hV x)

theorem contDiff_coordinateFluxDivergence (V : R3 → R3) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (coordinateFluxDivergence V) := by
  have h : coordinateFluxDivergence V = fun x => ∑ i, coordinateJacobianMatrix V x i i :=
    funext (coordinateFluxDivergence_eq_sum V (hV.differentiable (by simp)))
  rw [h]
  exact ContDiff.sum fun i _ => contDiff_coordinateJacobianMatrix_entry V hV i i

theorem contDiff_signedPiolaFlux (X Z : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (hZ : ContDiff ℝ ∞ Z) : ContDiff ℝ ∞ (signedPiolaFlux X Z) := by
  refine (contDiff_piLp 2).2 fun i => ?_
  change ContDiff ℝ ∞ fun y => ∑ k, (coordinateJacobianMatrix X y).adjugate i k * (Z (X y)) k
  exact ContDiff.sum fun k _ =>
    (contDiff_matrix_adjugate_entry _
      (fun a b => contDiff_coordinateJacobianMatrix_entry X hX a b) i k).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp (hZ.comp hX))

/-! ### Slices of functions on `ℝ × R3` -/

theorem fderiv_space_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : ℝ × R3 → F) (t : ℝ) (x w : R3) (hφ : DifferentiableAt ℝ φ (t, x)) :
    fderiv ℝ (fun z => φ (t, z)) x w = fderiv ℝ φ (t, x) (0, w) := by
  have h := HasFDerivAt.comp (g := φ) (f := fun z : R3 => (t, z)) x hφ.hasFDerivAt
    (hasFDerivAt_prodMk_right t x)
  rw [show (fun z => φ (t, z)) = φ ∘ (fun z : R3 => (t, z)) from rfl, h.fderiv]
  rfl

theorem hasDerivAt_time_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : ℝ × R3 → F) (t : ℝ) (x : R3) (hφ : DifferentiableAt ℝ φ (t, x)) :
    HasDerivAt (fun s => φ (s, x)) (fderiv ℝ φ (t, x) (1, 0)) t :=
  HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, x)) t hφ.hasFDerivAt
    ((hasDerivAt_id' t).prodMk (hasDerivAt_const t x))

theorem contDiff_fderiv_entry (H : ℝ × R3 → R3) (hH : ContDiff ℝ ∞ H) (u : ℝ × R3)
    (i : Fin 3) : ContDiff ℝ ∞ fun q => (fderiv ℝ H q u) i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp
    ((hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

theorem fderiv_entry (H : ℝ × R3 → R3) (hH : ContDiff ℝ ∞ H) (p u w : ℝ × R3) (i : Fin 3) :
    fderiv ℝ (fun q => (fderiv ℝ H q u) i) p w = (fderiv ℝ (fderiv ℝ H) p w u) i := by
  have hD : DifferentiableAt ℝ (fderiv ℝ H) p :=
    (hH.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p
  have he := hD.hasFDerivAt.clm_apply (hasFDerivAt_const u p)
  have hp := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp p he
  change fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i) ∘ (fun q => fderiv ℝ H q u)) p w = _
  rw [hp.fderiv]
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rfl

/-! ### Volume form of the flux -/

def jac (H : ℝ × R3 → R3) (p : ℝ × R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => (fderiv ℝ H p (0, cv j)) i

def vol (H : ℝ × R3 → R3) (Z : R3 → R3) (p : ℝ × R3) : ℝ :=
  (jac H p).det * coordinateFluxDivergence Z (H p)

def volFlux (H : ℝ × R3 → R3) (Z : R3 → R3) (t : ℝ) : ℝ :=
  ∫ x in ball (0 : R3) 1, vol H Z (t, x)

theorem jac_eq (H : ℝ × R3 → R3) (hH : ContDiff ℝ ∞ H) (t : ℝ) (x : R3) :
    jac H (t, x) = coordinateJacobianMatrix (fun z => H (t, z)) x := by
  ext i j
  unfold jac coordinateJacobianMatrix
  rw [fderiv_space_slice H t x _ (hH.differentiable (by simp) _)]
  rfl

theorem contDiff_det_fin_three {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (M : D → Matrix (Fin 3) (Fin 3) ℝ) (hM : ∀ i j, ContDiff ℝ ∞ fun p => M p i j) :
    ContDiff ℝ ∞ fun p => (M p).det := by
  simp only [Matrix.det_fin_three]
  have t1 := ((hM 0 0).mul (hM 1 1)).mul (hM 2 2)
  have t2 := ((hM 0 0).mul (hM 1 2)).mul (hM 2 1)
  have t3 := ((hM 0 1).mul (hM 1 0)).mul (hM 2 2)
  have t4 := ((hM 0 1).mul (hM 1 2)).mul (hM 2 0)
  have t5 := ((hM 0 2).mul (hM 1 0)).mul (hM 2 1)
  have t6 := ((hM 0 2).mul (hM 1 1)).mul (hM 2 0)
  exact ((((t1.sub t2).sub t3).add t4).add t5).sub t6

theorem contDiff_vol (H : ℝ × R3 → R3) (Z : R3 → R3) (hH : ContDiff ℝ ∞ H)
    (hZ : ContDiff ℝ ∞ Z) : ContDiff ℝ ∞ (vol H Z) :=
  (contDiff_det_fin_three (jac H) fun i j => contDiff_fderiv_entry H hH (0, cv j) i).mul
    ((contDiff_coordinateFluxDivergence Z hZ).comp hH)

theorem piolaSphereFlux_eq_volFlux (H : ℝ × R3 → R3) (Z : R3 → R3) (hH : ContDiff ℝ ∞ H)
    (hZ : ContDiff ℝ ∞ Z) (t : ℝ) : piolaSphereFlux H Z t = volFlux H Z t := by
  have hX : ContDiff ℝ ∞ (fun z => H (t, z)) := hH.comp (contDiff_const.prodMk contDiff_id)
  unfold piolaSphereFlux volFlux
  rw [← integral_ball_coordinateFluxDivergence _ (contDiff_signedPiolaFlux _ Z hX hZ)]
  refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
  rw [coordinateFluxDivergence_signedPiolaFlux _ Z hX hZ x]
  unfold vol
  rw [jac_eq H hH t x]

/-! ### H3: transport identity -/

theorem hasDerivAt_det_fin_three (α : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (α' : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ)
    (h : ∀ i j, HasDerivAt (fun r => α r i j) (α' i j) s) :
    HasDerivAt (fun r => (α r).det) (∑ i, ∑ j, (α s).adjugate j i * α' i j) s := by
  have t1 := ((h 0 0).mul (h 1 1)).mul (h 2 2)
  have t2 := ((h 0 0).mul (h 1 2)).mul (h 2 1)
  have t3 := ((h 0 1).mul (h 1 0)).mul (h 2 2)
  have t4 := ((h 0 1).mul (h 1 2)).mul (h 2 0)
  have t5 := ((h 0 2).mul (h 1 0)).mul (h 2 1)
  have t6 := ((h 0 2).mul (h 1 1)).mul (h 2 0)
  have key := ((((t1.sub t2).sub t3).add t4).add t5).sub t6
  refine (key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)).congr_deriv ?_
  · simp [Matrix.det_fin_three]
  · simp [Fin.sum_univ_succ, Matrix.adjugate_fin_three]
    ring

theorem transport_algebra (A T : Matrix (Fin 3) (Fin 3) ℝ) (V L : Fin 3 → ℝ) (F : ℝ) :
    (∑ i, ∑ k, A.adjugate i k * (F * T k i + V k * ∑ b, A b i * L b)) =
      (∑ i, ∑ j, A.adjugate j i * T i j) * F + A.det * ∑ b, V b * L b := by
  simp [Fin.sum_univ_succ, Matrix.adjugate_fin_three, Matrix.det_fin_three]
  ring

theorem hasDerivAt_vol_time (H : ℝ × R3 → R3) (Z : R3 → R3) (hH : ContDiff ℝ ∞ H)
    (hZ : ContDiff ℝ ∞ Z) (t : ℝ) (x : R3) :
    HasDerivAt (fun s => vol H Z (s, x))
      ((∑ i, ∑ j, (jac H (t, x)).adjugate j i *
          (fderiv ℝ (fderiv ℝ H) (t, x) (1, 0) (0, cv j)) i) *
          coordinateFluxDivergence Z (H (t, x)) +
        (jac H (t, x)).det * ∑ b, (fderiv ℝ H (t, x) (1, 0)) b *
          fderiv ℝ (coordinateFluxDivergence Z) (H (t, x)) (cv b)) t := by
  have hA : ∀ i j, HasDerivAt (fun s => jac H (s, x) i j)
      ((fderiv ℝ (fderiv ℝ H) (t, x) (1, 0) (0, cv j)) i) t := by
    intro i j
    have h := hasDerivAt_time_slice (fun q => (fderiv ℝ H q (0, cv j)) i) t x
      ((contDiff_fderiv_entry H hH (0, cv j) i).differentiable (by simp) _)
    rw [fderiv_entry H hH] at h
    exact h
  have hdet := hasDerivAt_det_fin_three (fun s => jac H (s, x)) _ t hA
  have hf := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => H (s, x)) t
    ((contDiff_coordinateFluxDivergence Z hZ).differentiable (by simp) (H (t, x))).hasFDerivAt
    (hasDerivAt_time_slice H t x (hH.differentiable (by simp) _))
  rw [clm_apply_eq_sum] at hf
  exact hdet.mul hf

def transportField (H : ℝ × R3 → R3) (Z : R3 → R3) (t : ℝ) (y : R3) : R3 :=
  WithLp.toLp 2 fun i => ∑ k, (coordinateJacobianMatrix (fun z => H (t, z)) y).adjugate i k *
    (coordinateFluxDivergence Z (H (t, y)) * (fderiv ℝ H (t, y) (1, 0)) k)

theorem contDiff_transportField (H : ℝ × R3 → R3) (Z : R3 → R3) (hH : ContDiff ℝ ∞ H)
    (hZ : ContDiff ℝ ∞ Z) (t : ℝ) : ContDiff ℝ ∞ (transportField H Z t) := by
  have hX : ContDiff ℝ ∞ (fun z => H (t, z)) := hH.comp (contDiff_const.prodMk contDiff_id)
  refine (contDiff_piLp 2).2 fun i => ?_
  change ContDiff ℝ ∞ fun y => ∑ k, (coordinateJacobianMatrix (fun z => H (t, z)) y).adjugate i k *
    (coordinateFluxDivergence Z (H (t, y)) * (fderiv ℝ H (t, y) (1, 0)) k)
  exact ContDiff.sum fun k _ =>
    (contDiff_matrix_adjugate_entry _
      (fun a b => contDiff_coordinateJacobianMatrix_entry _ hX a b) i k).mul
      (((contDiff_coordinateFluxDivergence Z hZ).comp hX).mul
        ((contDiff_fderiv_entry H hH (1, 0) k).comp (contDiff_const.prodMk contDiff_id)))

theorem coordinateFluxDivergence_transportField (H : ℝ × R3 → R3) (Z : R3 → R3)
    (hH : ContDiff ℝ ∞ H) (hZ : ContDiff ℝ ∞ Z) (t : ℝ) (x : R3) :
    coordinateFluxDivergence (transportField H Z t) x =
      ∑ i, ∑ k, (coordinateJacobianMatrix (fun z => H (t, z)) x).adjugate i k *
        (coordinateFluxDivergence Z (H (t, x)) *
            (fderiv ℝ (fderiv ℝ H) (t, x) (1, 0) (0, cv i)) k +
          (fderiv ℝ H (t, x) (1, 0)) k * ∑ b, coordinateJacobianMatrix (fun z => H (t, z)) x b i *
            fderiv ℝ (coordinateFluxDivergence Z) (H (t, x)) (cv b)) := by
  have hX : ContDiff ℝ ∞ (fun z => H (t, z)) := hH.comp (contDiff_const.prodMk contDiff_id)
  let C : R3 → Matrix (Fin 3) (Fin 3) ℝ :=
    fun y => (coordinateJacobianMatrix (fun z => H (t, z)) y).adjugate
  let w : Fin 3 → R3 → ℝ :=
    fun k y => coordinateFluxDivergence Z (H (t, y)) * (fderiv ℝ H (t, y) (1, 0)) k
  have hC (i k : Fin 3) : DifferentiableAt ℝ (fun y => C y i k) x :=
    (contDiff_matrix_adjugate_entry _
      (fun a b => contDiff_coordinateJacobianMatrix_entry _ hX a b) i k).differentiable
        (by simp) x
  have hfX : ContDiff ℝ ∞ (fun y => coordinateFluxDivergence Z (H (t, y))) :=
    (contDiff_coordinateFluxDivergence Z hZ).comp hX
  have hV (k : Fin 3) : ContDiff ℝ ∞ (fun y => (fderiv ℝ H (t, y) (1, 0)) k) :=
    (contDiff_fderiv_entry H hH (1, 0) k).comp (contDiff_const.prodMk contDiff_id)
  have hw (k : Fin 3) : DifferentiableAt ℝ (w k) x :=
    (hfX.mul (hV k)).differentiable (by simp) x
  have hterm (i k : Fin 3) :
      fderiv ℝ (fun y => C y i k * w k y) x (cv i) =
        C x i k * fderiv ℝ (w k) x (cv i) + w k x * fderiv ℝ (fun y => C y i k) x (cv i) := by
    rw [fderiv_fun_mul (hC i k) (hw k)]
    rfl
  have hzero : (∑ i : Fin 3, ∑ k : Fin 3,
      w k x * fderiv ℝ (fun y => C y i k) x (cv i)) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hz (k : Fin 3) : (∑ i : Fin 3, fderiv ℝ (fun y => C y i k) x (cv i)) = 0 :=
      coordinateJacobianMatrix_adjugate_column_divergence _ hX x k
    simp_rw [hz, mul_zero]
    exact Finset.sum_const_zero
  have hwder (i k : Fin 3) : fderiv ℝ (w k) x (cv i) =
      coordinateFluxDivergence Z (H (t, x)) *
          (fderiv ℝ (fderiv ℝ H) (t, x) (1, 0) (0, cv i)) k +
        (fderiv ℝ H (t, x) (1, 0)) k * ∑ b, coordinateJacobianMatrix (fun z => H (t, z)) x b i *
          fderiv ℝ (coordinateFluxDivergence Z) (H (t, x)) (cv b) := by
    have hfx : DifferentiableAt ℝ (fun y => coordinateFluxDivergence Z (H (t, y))) x :=
      hfX.differentiable (by simp) x
    have hvx : DifferentiableAt ℝ (fun y => (fderiv ℝ H (t, y) (1, 0)) k) x :=
      (hV k).differentiable (by simp) x
    have hsym : fderiv ℝ (fderiv ℝ H) (t, x) (0, cv i) (1, 0) =
        fderiv ℝ (fderiv ℝ H) (t, x) (1, 0) (0, cv i) :=
      (hH.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _
    have h1 : fderiv ℝ (fun y => (fderiv ℝ H (t, y) (1, 0)) k) x (cv i) =
        (fderiv ℝ (fderiv ℝ H) (t, x) (1, 0) (0, cv i)) k := by
      rw [fderiv_space_slice (fun q => (fderiv ℝ H q (1, 0)) k) t x _
        ((contDiff_fderiv_entry H hH (1, 0) k).differentiable (by simp) _),
        fderiv_entry H hH, hsym]
    have h2 : fderiv ℝ (fun y => coordinateFluxDivergence Z (H (t, y))) x (cv i) =
        ∑ b, coordinateJacobianMatrix (fun z => H (t, z)) x b i *
          fderiv ℝ (coordinateFluxDivergence Z) (H (t, x)) (cv b) := by
      have hc := HasFDerivAt.comp (f := fun z => H (t, z)) x
        ((contDiff_coordinateFluxDivergence Z hZ).differentiable (by simp) (H (t, x))).hasFDerivAt
        (hX.differentiable (by simp) x).hasFDerivAt
      rw [show (fun y => coordinateFluxDivergence Z (H (t, y))) =
        coordinateFluxDivergence Z ∘ (fun z => H (t, z)) from rfl, hc.fderiv,
        ContinuousLinearMap.comp_apply, clm_apply_eq_sum]
      rfl
    show fderiv ℝ (fun y => coordinateFluxDivergence Z (H (t, y)) *
      (fderiv ℝ H (t, y) (1, 0)) k) x (cv i) = _
    rw [fderiv_fun_mul hfx hvx, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul, h1, h2]
  have hsum (i : Fin 3) := fderiv_fun_sum (u := Finset.univ)
    (A := fun k y => C y i k * w k y) (fun k _ => (hC i k).mul (hw k))
  show (∑ i : Fin 3, fderiv ℝ (fun y => ∑ k : Fin 3, C y i k * w k y) x (cv i)) = _
  simp_rw [hsum]
  simp only [ContinuousLinearMap.sum_apply]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]
  rw [hzero, add_zero]
  simp_rw [hwder]
  rfl

theorem fderiv_vol_time (H : ℝ × R3 → R3) (Z : R3 → R3) (hH : ContDiff ℝ ∞ H)
    (hZ : ContDiff ℝ ∞ Z) (t : ℝ) (x : R3) :
    fderiv ℝ (vol H Z) (t, x) (1, 0) = coordinateFluxDivergence (transportField H Z t) x := by
  rw [(hasDerivAt_time_slice (vol H Z) t x
      ((contDiff_vol H Z hH hZ).differentiable (by simp) _)).unique
      (hasDerivAt_vol_time H Z hH hZ t x),
    coordinateFluxDivergence_transportField H Z hH hZ t x, jac_eq H hH t x]
  exact (transport_algebra (coordinateJacobianMatrix (fun z => H (t, z)) x)
    (Matrix.of fun i j => (fderiv ℝ (fderiv ℝ H) (t, x) (1, 0) (0, cv j)) i)
    (fun k => (fderiv ℝ H (t, x) (1, 0)) k)
    (fun b => fderiv ℝ (coordinateFluxDivergence Z) (H (t, x)) (cv b))
    (coordinateFluxDivergence Z (H (t, x)))).symm

/-! ### H4: differentiating the fixed-ball integral -/

theorem hasDerivAt_volFlux (H : ℝ × R3 → R3) (Z : R3 → R3) (hH : ContDiff ℝ ∞ H)
    (hZ : ContDiff ℝ ∞ Z) (t : ℝ) :
    HasDerivAt (volFlux H Z)
      (∫ x in ball (0 : R3) 1, fderiv ℝ (vol H Z) (t, x) (1, 0)) t := by
  have hv : ContDiff ℝ ∞ (vol H Z) := contDiff_vol H Z hH hZ
  have hc : Continuous fun p : ℝ × R3 => fderiv ℝ (vol H Z) p (1, 0) :=
    (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t 1).prod
    (isCompact_closedBall (0 : R3) 1)).exists_bound_of_continuousOn hc.continuousOn
  have hint (g : R3 → ℝ) (hg : Continuous g) :
      Integrable g (volume.restrict (ball (0 : R3) 1)) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall (0 : R3) 1)).mono_set
      ball_subset_closedBall
  have hslice (s : ℝ) : Continuous fun x : R3 => vol H Z (s, x) :=
    hv.continuous.comp (continuous_const.prodMk continuous_id)
  show HasDerivAt (fun s => ∫ x in ball (0 : R3) 1, vol H Z (s, x)) _ t
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (ball (0 : R3) 1))
    (F := fun s x => vol H Z (s, x)) (F' := fun s x => fderiv ℝ (vol H Z) (s, x) (1, 0))
    (bound := fun _ => C) (ball_mem_nhds t zero_lt_one) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun s => (hslice s).aestronglyMeasurable
  · exact hint _ (hslice t)
  · exact (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx s hs
    exact hC (s, x) ⟨ball_subset_closedBall hs, ball_subset_closedBall hx⟩
  · exact hint _ continuous_const
  · exact ae_of_all _ fun x s _ =>
      hasDerivAt_time_slice (vol H Z) s x (hv.differentiable (by simp) _)

theorem piolaSphereFlux_eq_of_divergence_eq_zero
    (H : ℝ × R3 → R3) (Z : R3 → R3)
    (hH : ContDiff ℝ ∞ H) (hZ : ContDiff ℝ ∞ Z)
    (hJ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall (0 : R3) 1,
      IsUnit (coordinateJacobianMatrix (fun z => H (t,z)) x).det)
    (hDiv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ theta : UnitSphere,
      coordinateFluxDivergence Z (H (t,theta.val)) = 0) :
    piolaSphereFlux H Z 1 = piolaSphereFlux H Z 0
    := by
  have hderiv : ∀ t, HasDerivAt (volFlux H Z)
      (∫ x in ball (0 : R3) 1, coordinateFluxDivergence (transportField H Z t) x) t := by
    intro t
    have h := hasDerivAt_volFlux H Z hH hZ t
    simp_rw [fderiv_vol_time H Z hH hZ t] at h
    exact h
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (volFlux H Z) _ zero_lt_one
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt) (fun t _ => hderiv t)
  have hcI : c ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hc
  have hzero : (∫ x in ball (0 : R3) 1,
      coordinateFluxDivergence (transportField H Z c) x) = 0 := by
    rw [integral_ball_coordinateFluxDivergence _ (contDiff_transportField H Z hH hZ c)]
    have hT : ∀ θ : UnitSphere, transportField H Z c θ.val = 0 := by
      intro θ
      simp [transportField, hDiv c hcI θ]
      rfl
    simp [hT]
  rw [piolaSphereFlux_eq_volFlux H Z hH hZ, piolaSphereFlux_eq_volFlux H Z hH hZ]
  rw [hzero, sub_zero, div_one] at hc'
  linarith

end OAI.AnisotropicCalderon.CurvedSurfaceTransfer


namespace OAI.AnisotropicCalderon.CurvedSurfaceTransfer
open EnergyBridge ConnectionError SphereHarmonic RadialTestIntegration

/-- Boundary-only oriented Piola flux invariance; no spatial invertibility is needed. -/
theorem piolaSphereFlux_eq_of_boundary_divergence_eq_zero
    (H : ℝ × R3 → R3) (Z : R3 → R3)
    (hH : ContDiff ℝ ∞ H) (hZ : ContDiff ℝ ∞ Z)
    (hDiv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ theta : UnitSphere,
      coordinateFluxDivergence Z (H (t,theta.val)) = 0) :
    piolaSphereFlux H Z 1 = piolaSphereFlux H Z 0
    := by
  have hderiv : ∀ t, HasDerivAt (volFlux H Z)
      (∫ x in ball (0 : R3) 1, coordinateFluxDivergence (transportField H Z t) x) t := by
    intro t
    have h := hasDerivAt_volFlux H Z hH hZ t
    simp_rw [fderiv_vol_time H Z hH hZ t] at h
    exact h
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (volFlux H Z) _ zero_lt_one
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt) (fun t _ => hderiv t)
  have hcI : c ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hc
  have hzero : (∫ x in ball (0 : R3) 1,
      coordinateFluxDivergence (transportField H Z c) x) = 0 := by
    rw [integral_ball_coordinateFluxDivergence _ (contDiff_transportField H Z hH hZ c)]
    have hT : ∀ θ : UnitSphere, transportField H Z c θ.val = 0 := by
      intro θ
      simp [transportField, hDiv c hcI θ]
      rfl
    simp [hT]
  rw [piolaSphereFlux_eq_volFlux H Z hH hZ, piolaSphereFlux_eq_volFlux H Z hH hZ]
  rw [hzero, sub_zero, div_one] at hc'
  linarith

end OAI.AnisotropicCalderon.CurvedSurfaceTransfer
