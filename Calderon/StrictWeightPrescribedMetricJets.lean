import Calderon.StrictWeightMetricCondition
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Operator.Prod

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology
open scoped ContDiff InnerProductSpace Matrix.Norms.Operator
namespace OAI.AnisotropicCalderon
open MetricVolume

theorem exists_contDiff_prescribed_metricHessian
    (g : MatrixField) (p : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun x => g x i j) p)
    (hs : ∀ᶠ x in 𝓝 p, (g x).IsHermitian)
    (ell : R3 →L[ℝ] ℝ) (P : R3 →L[ℝ] R3 →L[ℝ] ℝ)
    (hP : ∀ X Y : R3, P X Y = P Y X) :
    let Gamma := ConnectionError.coordinateConnectionField
      (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g))
      (MetricOperator.metricOperatorField g) p
    ∃ theta : R3 → ℝ,
      ContDiff ℝ ∞ theta ∧ theta p = 0 ∧ fderiv ℝ theta p = ell ∧
      (∀ x : R3, theta x = ell (x-p) +
        (1/2 : ℝ) * (P (x-p) (x-p) + ell (Gamma (x-p) (x-p)))) ∧
      (∀ X Y : R3,
        RadiusProfile.coordinateHessian theta (fun U V => Gamma U V) p X Y = P X Y) ∧
      (∀ i : Fin 3, pd i theta p = ell (coordinateVector i)) ∧
      (ell ≠ 0 → grad theta p ≠ 0) := by
  classical
  intro Gamma
  let D : R3 →L[ℝ] R3 →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ R3 R3 ℝ) ell).comp Gamma
  let B : R3 →L[ℝ] R3 →L[ℝ] ℝ := P + D
  have hB (X Y : R3) : B X Y = P X Y + ell (Gamma X Y) := rfl
  have hGamma (X Y : R3) : Gamma X Y = Gamma Y X :=
    actualMetricConnection_symmetric_local g p hg hs X Y
  have hSym (X Y : R3) : B X Y = B Y X := by
    rw [hB X Y,hB Y X,hP X Y,hGamma X Y]
  let theta : R3 → ℝ := fun x => ell (x-p) + (1/2 : ℝ) * B (x-p) (x-p)
  have hTrans : ContDiff ℝ ∞ (fun x : R3 => x-p) := contDiff_id.sub contDiff_const
  have hSmooth : ContDiff ℝ ∞ theta :=
    (ell.contDiff.comp hTrans).add
      (contDiff_const.mul ((B.contDiff.comp hTrans).clm_apply hTrans))
  have hDeriv (x : R3) : HasFDerivAt theta (ell + B (x-p)) x := by
    have hT : HasFDerivAt (fun y : R3 => y-p) (ContinuousLinearMap.id ℝ R3) x :=
      (hasFDerivAt_id x).sub_const p
    have hEll : HasFDerivAt (fun y : R3 => ell (y-p)) ell x := by
      have hOuter : HasFDerivAt (fun v : R3 => ell v) ell (x-p) :=
        ContinuousLinearMap.hasFDerivAt ell
      have hComp := HasFDerivAt.comp (f := fun y : R3 => y-p)
        (f' := ContinuousLinearMap.id ℝ R3) (g := fun v : R3 => ell v) (g' := ell)
        x hOuter hT
      simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using hComp
    have hQuad := B.hasFDerivAt_of_bilinear hT hT
    have hA : (1/2 : ℝ) •
        (B.precompR R3 (x-p) (ContinuousLinearMap.id ℝ R3) +
          B.precompL R3 (ContinuousLinearMap.id ℝ R3) (x-p)) = B (x-p) := by
      apply ContinuousLinearMap.ext
      intro X
      change (1/2 : ℝ) * (B (x-p) X + B X (x-p)) = B (x-p) X
      rw [hSym X (x-p)]
      ring
    have h := hEll.add (hQuad.const_smul (1/2 : ℝ))
    rw [hA] at h
    have hFunction : ((fun y : R3 => ell (y-p)) +
        (1/2 : ℝ) • (fun y : R3 => B (y-p) (y-p))) = theta := by
      funext y
      rfl
    rw [hFunction] at h
    exact h
  have hDf : fderiv ℝ theta = (fun x : R3 => ell + B (x-p)) :=
    funext (fun x => (hDeriv x).fderiv)
  have hFirst : fderiv ℝ theta p = ell := by
    rw [hDf]
    simp only [sub_self,map_zero,add_zero]
  have hSecond : fderiv ℝ (fderiv ℝ theta) p = B := by
    rw [hDf]
    have hT : HasFDerivAt (fun x : R3 => x-p) (ContinuousLinearMap.id ℝ R3) p :=
      (hasFDerivAt_id p).sub_const p
    have hOuter : HasFDerivAt (fun v : R3 => B v) B (p-p) :=
      ContinuousLinearMap.hasFDerivAt B
    have hComp := HasFDerivAt.comp (f := fun x : R3 => x-p)
      (f' := ContinuousLinearMap.id ℝ R3) (g := fun v : R3 => B v) (g' := B)
      p hOuter hT
    have hBderiv : HasFDerivAt (fun x : R3 => B (x-p)) B p := by
      simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using hComp
    exact (hBderiv.const_add ell).fderiv
  have hPD (i : Fin 3) : pd i theta p = ell (coordinateVector i) := by
    change fderiv ℝ theta p (coordinateVector i) = ell (coordinateVector i)
    rw [hFirst]
  refine ⟨theta,hSmooth,?_,hFirst,?_,?_,hPD,?_⟩
  · simp only [theta,sub_self,map_zero,mul_zero,add_zero]
  · intro x
    change ell (x-p) + (1/2 : ℝ) * B (x-p) (x-p) =
      ell (x-p) + (1/2 : ℝ) * (P (x-p) (x-p) + ell (Gamma (x-p) (x-p)))
    rw [hB]
  · intro X Y
    unfold RadiusProfile.coordinateHessian
    rw [hSecond,hFirst,hB]
    ring
  · intro hell hGrad
    apply hell
    apply ContinuousLinearMap.ext
    intro V
    change ell V = 0
    rw [covector_coordinate_sum ell V]
    apply Finset.sum_eq_zero
    intro i _
    have hi : ell (coordinateVector i) = 0 := by
      rw [← hPD i]
      exact congrFun hGrad i
    simp only [hi,mul_zero]

theorem exists_local_product_phase_gap
    (g1 g2 : MatrixField) (x0 y0 : R3)
    (hg1 : ∀ i j, DifferentiableAt ℝ (fun x => g1 x i j) x0)
    (hg2 : ∀ i j, DifferentiableAt ℝ (fun y => g2 y i j) y0)
    (hs1 : ∀ᶠ x in 𝓝 x0, (g1 x).IsHermitian)
    (hs2 : ∀ᶠ y in 𝓝 y0, (g2 y).IsHermitian)
    (hp1 : (g1 x0).PosDef) (hp2 : (g2 y0).PosDef)
    (U : Set (R3 × R3)) (hU : IsOpen U) (h0U : (x0,y0) ∈ U)
    (rho : R3 × R3 → ℝ) (hrho : ContDiffOn ℝ ∞ rho U) (hrho0 : rho (x0,y0) = 0)
    (P1 P2 : R3 →L[ℝ] R3 →L[ℝ] ℝ)
    (hP1 : ∀ X Y : R3, P1 X Y = P1 Y X)
    (hP2 : ∀ X Y : R3, P2 X Y = P2 Y X)
    (K : ℝ) (hK : 0 < K) :
    let ell : (R3 × R3) →L[ℝ] ℝ := fderiv ℝ rho (x0,y0)
    let ell1 : R3 →L[ℝ] ℝ := ell.comp (ContinuousLinearMap.inl ℝ R3 R3)
    let ell2 : R3 →L[ℝ] ℝ := ell.comp (ContinuousLinearMap.inr ℝ R3 R3)
    let M1 : R3 →L[ℝ] R3 := MetricOperator.metricOperatorField g1 x0
    let M2 : R3 →L[ℝ] R3 := MetricOperator.metricOperatorField g2 y0
    let Gamma1 := ConnectionError.coordinateConnectionField
      (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g1))
      (MetricOperator.metricOperatorField g1) x0
    let Gamma2 := ConnectionError.coordinateConnectionField
      (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g2))
      (MetricOperator.metricOperatorField g2) y0
    let b1 : R3 := MetricOperator.matrixOperatorMap ((g1 x0)⁻¹)
      (WithLp.toLp 2 (fun i : Fin 3 => ell1 (coordinateVector i)))
    let b2 : R3 := MetricOperator.matrixOperatorMap ((g2 y0)⁻¹)
      (WithLp.toLp 2 (fun i : Fin 3 => ell2 (coordinateVector i)))
    let a1 : R3 := (⟪M1 b1,b1⟫_ℝ)⁻¹ • b1
    let a2 : R3 := (⟪M2 b2,b2⟫_ℝ)⁻¹ • b2
    ell1 ≠ 0 → ell2 ≠ 0 →
    (∀ v : R3, ⟪M1 v,a1⟫_ℝ = 0 → ⟪M1 v,v⟫_ℝ = ⟪M1 a1,a1⟫_ℝ →
      0 < P1 a1 a1 + P1 v v) →
    (∀ v : R3, ⟪M2 v,a2⟫_ℝ = 0 → ⟪M2 v,v⟫_ℝ = ⟪M2 a2,a2⟫_ℝ →
      0 < P2 a2 a2 + P2 v v) →
    (∀ W : R3 × R3, W ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ rho) (x0,y0) W W -
        ell (Gamma1 W.1 W.1, Gamma2 W.2 W.2) + K * (ell W)^2 -
        P1 W.1 W.1 - P2 W.2 W.2) →
    ∃ (theta1 theta2 : R3 → ℝ) (c r : ℝ),
      ContDiff ℝ ∞ theta1 ∧ ContDiff ℝ ∞ theta2 ∧
      theta1 x0 = 0 ∧ theta2 y0 = 0 ∧
      fderiv ℝ theta1 x0 = ell1 ∧ fderiv ℝ theta2 y0 = ell2 ∧
      (∀ x : R3, theta1 x = ell1 (x-x0) +
        (1/2 : ℝ) * (P1 (x-x0) (x-x0) + ell1 (Gamma1 (x-x0) (x-x0)))) ∧
      (∀ y : R3, theta2 y = ell2 (y-y0) +
        (1/2 : ℝ) * (P2 (y-y0) (y-y0) + ell2 (Gamma2 (y-y0) (y-y0)))) ∧
      (∀ X Y : R3, RadiusProfile.coordinateHessian theta1
        (fun A B => Gamma1 A B) x0 X Y = P1 X Y) ∧
      (∀ X Y : R3, RadiusProfile.coordinateHessian theta2
        (fun A B => Gamma2 A B) y0 X Y = P2 X Y) ∧
      (∀ i : Fin 3, pd i theta1 x0 = ell1 (coordinateVector i)) ∧
      (∀ i : Fin 3, pd i theta2 y0 = ell2 (coordinateVector i)) ∧
      grad theta1 x0 ≠ 0 ∧ grad theta2 y0 ≠ 0 ∧
      (let b : R3 := MetricOperator.matrixOperatorMap ((g1 x0)⁻¹)
          (WithLp.toLp 2 (grad theta1 x0))
       let e : R3 := (Real.sqrt ⟪M1 b,b⟫_ℝ)⁻¹ • b
       ∀ v : R3, ⟪M1 v,e⟫_ℝ = 0 → ⟪M1 v,v⟫_ℝ = 1 →
         0 < RadiusProfile.coordinateHessian theta1
           (fun A B => Gamma1 A B) x0 e e +
           RadiusProfile.coordinateHessian theta1 (fun A B => Gamma1 A B) x0 v v) ∧
      (let b : R3 := MetricOperator.matrixOperatorMap ((g2 y0)⁻¹)
          (WithLp.toLp 2 (grad theta2 y0))
       let e : R3 := (Real.sqrt ⟪M2 b,b⟫_ℝ)⁻¹ • b
       ∀ v : R3, ⟪M2 v,e⟫_ℝ = 0 → ⟪M2 v,v⟫_ℝ = 1 →
         0 < RadiusProfile.coordinateHessian theta2
           (fun A B => Gamma2 A B) y0 e e +
           RadiusProfile.coordinateHessian theta2 (fun A B => Gamma2 A B) y0 v v) ∧
      0 < c ∧ 0 < r ∧ Metric.closedBall (x0,y0) r ⊆ U ∧
      (∀ z : R3 × R3, z ∈ Metric.closedBall (x0,y0) r →
        theta1 z.1 + theta2 z.2 ≤ rho z + K*(rho z)^2/2 -
          c*(‖z.1-x0‖^2 + ‖z.2-y0‖^2)) ∧
      (∀ z : R3 × R3, z ∈ Metric.closedBall (x0,y0) r →
        (0 < rho z + K*(rho z)^2/2 ↔ 0 < rho z)) := by
  classical
  intro ell ell1 ell2 M1 M2 Gamma1 Gamma2 b1 b2 a1 a2
  intro hell1 hell2 hStrict1 hStrict2 hGap
  obtain ⟨theta1,hSmooth1,hZero1,hFirst1,hFormula1,hHess1,hPD1,hGrad1⟩ :=
    exists_contDiff_prescribed_metricHessian g1 x0 hg1 hs1 ell1 P1 hP1
  obtain ⟨theta2,hSmooth2,hZero2,hFirst2,hFormula2,hHess2,hPD2,hGrad2⟩ :=
    exists_contDiff_prescribed_metricHessian g2 y0 hg2 hs2 ell2 P2 hP2
  have hG1 : grad theta1 x0 ≠ 0 := hGrad1 hell1
  have hG2 : grad theta2 y0 ≠ 0 := hGrad2 hell2
  have hGradEq1 : grad theta1 x0 = (fun i : Fin 3 => ell1 (coordinateVector i)) :=
    funext hPD1
  have hGradEq2 : grad theta2 y0 = (fun i : Fin 3 => ell2 (coordinateVector i)) :=
    funext hPD2
  have unitStrict : ∀ (g : MatrixField) (p : R3) (hp : (g p).PosDef)
      (theta : R3 → ℝ) (hGrad : grad theta p ≠ 0)
      (P : R3 →L[ℝ] R3 →L[ℝ] ℝ) (Gamma : R3 →L[ℝ] R3 →L[ℝ] R3),
      (∀ X Y : R3,
        RadiusProfile.coordinateHessian theta (fun A B => Gamma A B) p X Y = P X Y) →
      (let M := MetricOperator.metricOperatorField g p
       let b : R3 := MetricOperator.matrixOperatorMap ((g p)⁻¹)
         (WithLp.toLp 2 (grad theta p))
       let a : R3 := (⟪M b,b⟫_ℝ)⁻¹ • b
       ∀ v : R3, ⟪M v,a⟫_ℝ = 0 → ⟪M v,v⟫_ℝ = ⟪M a,a⟫_ℝ →
         0 < P a a + P v v) →
      (let M := MetricOperator.metricOperatorField g p
       let b : R3 := MetricOperator.matrixOperatorMap ((g p)⁻¹)
         (WithLp.toLp 2 (grad theta p))
       let e : R3 := (Real.sqrt ⟪M b,b⟫_ℝ)⁻¹ • b
       ∀ v : R3, ⟪M v,e⟫_ℝ = 0 → ⟪M v,v⟫_ℝ = 1 →
         0 < RadiusProfile.coordinateHessian theta (fun A B => Gamma A B) p e e +
           RadiusProfile.coordinateHessian theta (fun A B => Gamma A B) p v v) := by
    intro g p hp theta hGrad P Gamma hH hS M b e
    let n : ℝ := ⟪M b,b⟫_ℝ
    let t : ℝ := (Real.sqrt n)⁻¹
    let a : R3 := n⁻¹ • b
    have hGA (V : R3) : M (MetricOperator.matrixOperatorMap ((g p)⁻¹) V) = V := by
      have hmat : g p * (g p)⁻¹ = 1 :=
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit)
      have hop : MetricOperator.matrixOperatorMap (g p) *
          MetricOperator.matrixOperatorMap ((g p)⁻¹) = 1 := by
        change MetricOperator.matrixOperatorAlgEquiv (g p) *
          MetricOperator.matrixOperatorAlgEquiv ((g p)⁻¹) = 1
        rw [← map_mul,hmat,map_one]
      change (MetricOperator.matrixOperatorMap (g p) *
        MetricOperator.matrixOperatorMap ((g p)⁻¹)) V = V
      rw [hop]
      rfl
    have hn : 0 < n := by
      change 0 < ⟪M (MetricOperator.matrixOperatorMap ((g p)⁻¹)
        (WithLp.toLp 2 (grad theta p))),
        MetricOperator.matrixOperatorMap ((g p)⁻¹) (WithLp.toLp 2 (grad theta p))⟫_ℝ
      rw [hGA]
      have h := hp.inv.dotProduct_mulVec_pos hGrad
      simpa only [EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,
        Pi.star_apply,star_trivial,dotProduct,Matrix.mulVec,matrixOperator_coordinate,
        PiLp.toLp_apply,mul_comm] using h
    have ht : 0 < t := inv_pos.mpr (Real.sqrt_pos.mpr hn)
    have htSquare : t^2 = n⁻¹ := by
      simp only [t,inv_pow,Real.sq_sqrt hn.le]
    have htn : t^2*n = 1 := by
      rw [htSquare,inv_mul_cancel₀ hn.ne']
    have he : e = t • b := rfl
    have ha : a = t • e := by
      rw [he,smul_smul,← pow_two,htSquare]
    have heUnit : ⟪M e,e⟫_ℝ = 1 := by
      rw [he]
      simp only [map_smul,inner_smul_left,inner_smul_right,conj_trivial]
      change t*(t*n) = 1
      nlinarith only [htn]
    have haNorm : ⟪M a,a⟫_ℝ = t^2 := by
      rw [ha]
      simp only [map_smul,inner_smul_left,inner_smul_right,conj_trivial,heUnit]
      ring
    change ∀ v : R3, ⟪M v,a⟫_ℝ = 0 → ⟪M v,v⟫_ℝ = ⟪M a,a⟫_ℝ →
      0 < P a a + P v v at hS
    intro v hvOrth hvUnit
    have hVorth : ⟪M (t • v),a⟫_ℝ = 0 := by
      rw [ha]
      simp only [map_smul,inner_smul_left,inner_smul_right,conj_trivial,hvOrth,mul_zero]
    have hVnorm : ⟪M (t • v),t • v⟫_ℝ = ⟪M a,a⟫_ℝ := by
      rw [haNorm]
      simp only [map_smul,inner_smul_left,inner_smul_right,conj_trivial,hvUnit]
      ring
    have hPositive := hS (t • v) hVorth hVnorm
    rw [ha] at hPositive
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul] at hPositive
    have hScaled : 0 < t^2 * (P e e + P v v) := by nlinarith only [hPositive]
    have hUnscaled : 0 < P e e + P v v :=
      pos_of_mul_pos_right hScaled (sq_nonneg t)
    rw [hH e e,hH v v]
    exact hUnscaled
  have hUnit1 := unitStrict g1 x0 hp1 theta1 hG1 P1 Gamma1 hHess1 (by
    simpa only [hGradEq1] using hStrict1)
  have hUnit2 := unitStrict g2 y0 hp2 theta2 hG2 P2 Gamma2 hHess2 (by
    simpa only [hGradEq2] using hStrict2)
  let E := R3 × R3
  let z0 : E := (x0,y0)
  let pr1 : E →L[ℝ] R3 := ContinuousLinearMap.fst ℝ R3 R3
  let pr2 : E →L[ℝ] R3 := ContinuousLinearMap.snd ℝ R3 R3
  let C1 : (R3 →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E R3 ℝ).flip pr1
  let C2 : (R3 →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E R3 ℝ).flip pr2
  let RhoD : E → E →L[ℝ] ℝ := fderiv ℝ rho
  let D1 : E → E →L[ℝ] ℝ := fun z => C1 (fderiv ℝ theta1 z.1)
  let D2 : E → E →L[ℝ] ℝ := fun z => C2 (fderiv ℝ theta2 z.2)
  let F : E → ℝ := fun z => rho z + (K/2) * (rho z * rho z) - theta1 z.1 - theta2 z.2
  let Aderiv : E → E →L[ℝ] ℝ := fun z =>
    RhoD z + (K/2) • (rho z • RhoD z + rho z • RhoD z) - D1 z - D2 z
  have hRhoAt : ContDiffAt ℝ ∞ rho z0 := hrho.contDiffAt (hU.mem_nhds h0U)
  have hRhoDiff (z : E) (hz : z ∈ U) : DifferentiableAt ℝ rho z :=
    (hrho.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hF : ContDiffOn ℝ ∞ F U :=
    ((hrho.add (contDiffOn_const.mul (hrho.mul hrho))).sub
      (hSmooth1.comp contDiff_fst).contDiffOn).sub
        (hSmooth2.comp contDiff_snd).contDiffOn
  have hDFat (z : E) (hz : z ∈ U) : fderiv ℝ F z = Aderiv z := by
    have hR : HasFDerivAt rho (RhoD z) z := (hRhoDiff z hz).hasFDerivAt
    have hT1 : HasFDerivAt (fun w : E => theta1 w.1) (D1 z) z := by
      have hOuter : HasFDerivAt theta1 (fderiv ℝ theta1 z.1) z.1 :=
        (hSmooth1.differentiable (by simp) z.1).hasFDerivAt
      have hInner : HasFDerivAt (fun w : E => w.1) pr1 z :=
        ContinuousLinearMap.hasFDerivAt pr1
      exact HasFDerivAt.comp (f := fun w : E => w.1) (f' := pr1)
        (g := theta1) (g' := fderiv ℝ theta1 z.1) z hOuter hInner
    have hT2 : HasFDerivAt (fun w : E => theta2 w.2) (D2 z) z := by
      have hOuter : HasFDerivAt theta2 (fderiv ℝ theta2 z.2) z.2 :=
        (hSmooth2.differentiable (by simp) z.2).hasFDerivAt
      have hInner : HasFDerivAt (fun w : E => w.2) pr2 z :=
        ContinuousLinearMap.hasFDerivAt pr2
      exact HasFDerivAt.comp (f := fun w : E => w.2) (f' := pr2)
        (g := theta2) (g' := fderiv ℝ theta2 z.2) z hOuter hInner
    have h := ((hR.add ((hR.mul hR).const_smul (K/2))).sub hT1).sub hT2
    have hFunction : ((rho + (K/2) • (rho*rho) - (fun w : E => theta1 w.1)) -
        (fun w : E => theta2 w.2)) = F := by
      funext w
      rfl
    rw [hFunction] at h
    simpa only [Aderiv,RhoD] using h.fderiv
  have hDFgerm : fderiv ℝ F =ᶠ[𝓝 z0] Aderiv := by
    filter_upwards [hU.mem_nhds h0U] with z hz
    exact hDFat z hz
  have hEllPair (X Y : R3) : ell (X,Y) = ell1 X + ell2 Y := by
    change ell (X,Y) = ell (X,0) + ell (0,Y)
    rw [← map_add]
    congr 1
    simp only [Prod.mk_add_mk,add_zero,zero_add]
  have hFzero : F z0 = 0 := by
    simp only [F,z0,hrho0,hZero1,hZero2,mul_zero,zero_add,sub_zero]
  have hDFzero : fderiv ℝ F z0 = 0 := by
    rw [hDFat z0 h0U]
    apply ContinuousLinearMap.ext
    intro W
    change ell W + (K/2) * (rho z0 * ell W + rho z0 * ell W) -
      (fderiv ℝ theta1 x0) W.1 - (fderiv ℝ theta2 y0) W.2 = 0
    rw [hrho0,hFirst1,hFirst2]
    have h := hEllPair W.1 W.2
    change ell W = ell1 W.1 + ell2 W.2 at h
    linarith only [h]
  have hSecond1 (X Y : R3) : fderiv ℝ (fderiv ℝ theta1) x0 X Y =
      P1 X Y + ell1 (Gamma1 X Y) := by
    have h := hHess1 X Y
    unfold RadiusProfile.coordinateHessian at h
    rw [hFirst1] at h
    linarith only [h]
  have hSecond2 (X Y : R3) : fderiv ℝ (fderiv ℝ theta2) y0 X Y =
      P2 X Y + ell2 (Gamma2 X Y) := by
    have h := hHess2 X Y
    unfold RadiusProfile.coordinateHessian at h
    rw [hFirst2] at h
    linarith only [h]
  have hRD : HasFDerivAt RhoD (fderiv ℝ (fderiv ℝ rho) z0) z0 :=
    ((hRhoAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hR : HasFDerivAt rho ell z0 := (hRhoDiff z0 h0U).hasFDerivAt
  have hD1 : HasFDerivAt D1
      (C1.comp ((fderiv ℝ (fderiv ℝ theta1) x0).comp pr1)) z0 := by
    have hTheta : HasFDerivAt (fderiv ℝ theta1)
        (fderiv ℝ (fderiv ℝ theta1) x0) x0 :=
      (((hSmooth1.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x0).hasFDerivAt
    have hP : HasFDerivAt (fun z : E => z.1) pr1 z0 :=
      ContinuousLinearMap.hasFDerivAt pr1
    have hFirst := HasFDerivAt.comp (f := fun z : E => z.1) (f' := pr1)
      (g := fderiv ℝ theta1) (g' := fderiv ℝ (fderiv ℝ theta1) x0) z0 hTheta hP
    have hOuter : HasFDerivAt (fun v : R3 →L[ℝ] ℝ => C1 v) C1 (fderiv ℝ theta1 x0) :=
      ContinuousLinearMap.hasFDerivAt C1
    exact HasFDerivAt.comp (f := fun z : E => fderiv ℝ theta1 z.1)
      (f' := (fderiv ℝ (fderiv ℝ theta1) x0).comp pr1)
      (g := fun v : R3 →L[ℝ] ℝ => C1 v) (g' := C1) z0 hOuter hFirst
  have hD2 : HasFDerivAt D2
      (C2.comp ((fderiv ℝ (fderiv ℝ theta2) y0).comp pr2)) z0 := by
    have hTheta : HasFDerivAt (fderiv ℝ theta2)
        (fderiv ℝ (fderiv ℝ theta2) y0) y0 :=
      (((hSmooth2.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y0).hasFDerivAt
    have hP : HasFDerivAt (fun z : E => z.2) pr2 z0 :=
      ContinuousLinearMap.hasFDerivAt pr2
    have hFirst := HasFDerivAt.comp (f := fun z : E => z.2) (f' := pr2)
      (g := fderiv ℝ theta2) (g' := fderiv ℝ (fderiv ℝ theta2) y0) z0 hTheta hP
    have hOuter : HasFDerivAt (fun v : R3 →L[ℝ] ℝ => C2 v) C2 (fderiv ℝ theta2 y0) :=
      ContinuousLinearMap.hasFDerivAt C2
    exact HasFDerivAt.comp (f := fun z : E => fderiv ℝ theta2 z.2)
      (f' := (fderiv ℝ (fderiv ℝ theta2) y0).comp pr2)
      (g := fun v : R3 →L[ℝ] ℝ => C2 v) (g' := C2) z0 hOuter hFirst
  have hScale := hR.smul hRD
  have hA := ((hRD.add ((hScale.add hScale).const_smul (K/2))).sub hD1).sub hD2
  have hAFunction : (RhoD + (K/2) • (rho • RhoD + rho • RhoD) - D1 - D2) = Aderiv := by
    funext z
    rfl
  rw [hAFunction] at hA
  let Q : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ F) z0
  have hQformula (W : E) : Q W W =
      fderiv ℝ (fderiv ℝ rho) z0 W W -
        ell (Gamma1 W.1 W.1,Gamma2 W.2 W.2) + K*(ell W)^2 -
          P1 W.1 W.1 - P2 W.2 W.2 := by
    have hQderiv : Q = fderiv ℝ Aderiv z0 := hDFgerm.fderiv_eq
    rw [hQderiv,hA.fderiv]
    change fderiv ℝ (fderiv ℝ rho) z0 W W +
      (K/2) * ((rho z0 * fderiv ℝ (fderiv ℝ rho) z0 W W + ell W * ell W) +
        (rho z0 * fderiv ℝ (fderiv ℝ rho) z0 W W + ell W * ell W)) -
      fderiv ℝ (fderiv ℝ theta1) x0 W.1 W.1 -
      fderiv ℝ (fderiv ℝ theta2) y0 W.2 W.2 = _
    rw [hrho0,hSecond1,hSecond2,hEllPair (Gamma1 W.1 W.1) (Gamma2 W.2 W.2)]
    ring
  have hQpositive (W : E) (hW : W ≠ 0) : 0 < Q W W := by
    rw [hQformula]
    exact hGap W hW
  have hQcontinuous : Continuous (fun W : E => Q W W) :=
    (Q.contDiff.clm_apply contDiff_id : ContDiff ℝ ∞ (fun W : E => Q W W)).continuous
  obtain ⟨m,hm,hSphere⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    hQcontinuous.continuousOn (fun W hW => hQpositive W (by
      have hNorm : ‖W‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hW
      intro hZero
      simp only [hZero,norm_zero] at hNorm
      norm_num at hNorm))
  have hQlower (W : E) : m*‖W‖^2 ≤ Q W W := by
    by_cases hW : W = 0
    · subst W
      simp only [norm_zero,map_zero]
      norm_num
    have hNorm : 0 < ‖W‖ := norm_pos_iff.mpr hW
    let V : E := ‖W‖⁻¹ • W
    have hV : ‖V‖ = 1 := by
      simp only [V,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hNorm),
        inv_mul_cancel₀ hNorm.ne']
    have hVSphere : V ∈ sphere (0 : E) 1 := by
      simpa only [mem_sphere,dist_zero_right] using hV
    have hMin := hSphere V hVSphere
    have hBack : ‖W‖ • V = W := by
      simp only [V,smul_smul,mul_inv_cancel₀ hNorm.ne',one_smul]
    have hScale : Q W W = ‖W‖^2 * Q V V := by
      calc
        Q W W = Q (‖W‖ • V) (‖W‖ • V) := by rw [hBack]
        _ = ‖W‖^2 * Q V V := by
          simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
          ring
    rw [hScale,mul_comm m (‖W‖^2)]
    exact mul_le_mul_of_nonneg_left hMin (sq_nonneg ‖W‖)
  have hFDsmooth : ContDiffOn ℝ ∞ (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by simp)
  have hFDDsmooth : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ F)) U :=
    hFDsmooth.fderiv_of_isOpen hU (by simp)
  have hQAt : ContinuousAt (fderiv ℝ (fderiv ℝ F)) z0 :=
    hFDDsmooth.continuousOn.continuousAt (hU.mem_nhds h0U)
  have hNearQ : ∀ᶠ z in 𝓝 z0, ‖fderiv ℝ (fderiv ℝ F) z - Q‖ < m/2 := by
    have hBall : ball Q (m/2) ∈ 𝓝 (fderiv ℝ (fderiv ℝ F) z0) :=
      ball_mem_nhds Q (half_pos hm)
    filter_upwards [hQAt.preimage_mem_nhds hBall] with z hz
    have hdist : dist (fderiv ℝ (fderiv ℝ F) z) Q < m/2 := mem_ball.mp hz
    have hdistEq : dist (fderiv ℝ (fderiv ℝ F) z) Q =
        ‖fderiv ℝ (fderiv ℝ F) z-Q‖ :=
      _root_.dist_eq_norm_sub (E := E →L[ℝ] E →L[ℝ] ℝ)
        (fderiv ℝ (fderiv ℝ F) z) Q
    exact hdistEq ▸ hdist
  have hRhoContinuous : ContinuousAt rho z0 := hRhoAt.continuousAt
  have hFactorContinuous : ContinuousAt (fun z : E => 1+K*rho z/2) z0 :=
    continuousAt_const.add ((continuousAt_const.mul hRhoContinuous).div_const 2)
  have hFactorAt0 : 0 < 1+K*rho z0/2 := by
    rw [hrho0]
    norm_num
  have hNearFactor : ∀ᶠ z in 𝓝 z0, 0 < 1+K*rho z/2 :=
    hFactorContinuous.eventually (lt_mem_nhds hFactorAt0)
  have hNear : {z : E | z ∈ U ∧ ‖fderiv ℝ (fderiv ℝ F) z - Q‖ < m/2 ∧
      0 < 1+K*rho z/2} ∈ 𝓝 z0 := by
    filter_upwards [hU.mem_nhds h0U,hNearQ,hNearFactor] with z hz hq hf
    exact ⟨hz,hq,hf⟩
  obtain ⟨alpha,halpha,hRoom⟩ := Metric.mem_nhds_iff.mp hNear
  let r : ℝ := alpha/2
  have hr : 0 < r := half_pos halpha
  have hClosedRoom (z : E) (hz : z ∈ closedBall z0 r) :
      z ∈ U ∧ ‖fderiv ℝ (fderiv ℝ F) z - Q‖ < m/2 ∧ 0 < 1+K*rho z/2 := by
    apply hRoom
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (half_lt_self halpha))
  have hHessianLower (z : E) (hz : z ∈ closedBall z0 r) (W : E) :
      (m/2)*‖W‖^2 ≤ fderiv ℝ (fderiv ℝ F) z W W := by
    let Err : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ F) z - Q
    have hError : |fderiv ℝ (fderiv ℝ F) z W W - Q W W| ≤ ‖Err‖*‖W‖^2 := by
      calc
        _ = ‖Err W W‖ := by
          simp only [Err,ContinuousLinearMap.sub_apply,Real.norm_eq_abs]
        _ ≤ ‖Err W‖*‖W‖ := (Err W).le_opNorm W
        _ ≤ (‖Err‖*‖W‖)*‖W‖ :=
          mul_le_mul_of_nonneg_right (Err.le_opNorm W) (norm_nonneg W)
        _ = ‖Err‖*‖W‖^2 := by ring
    have hErrorLower := neg_le_of_abs_le hError
    have hCompare : ‖Err‖*‖W‖^2 ≤ (m/2)*‖W‖^2 :=
      mul_le_mul_of_nonneg_right (hClosedRoom z hz).2.1.le (sq_nonneg ‖W‖)
    linarith only [hQlower W,hErrorLower,hCompare]
  have curveSecond : ∀ (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) (W : E) (t : ℝ),
      z0+t • W ∈ U →
      deriv (deriv (fun s : ℝ => f (z0+s • W))) t =
        fderiv ℝ (fderiv ℝ f) (z0+t • W) W W := by
    intro f hf W t htU
    let gamma : ℝ → E := fun s => z0+s • W
    have hGamma (s : ℝ) : HasDerivAt gamma W s := by
      simpa only [gamma,one_smul] using
        ((hasDerivAt_id' s).smul_const W).const_add z0
    have hNearGamma : ∀ᶠ s in 𝓝 t, gamma s ∈ U :=
      (hGamma t).continuousAt.preimage_mem_nhds (hU.mem_nhds htU)
    have hGerm : deriv (fun s : ℝ => f (gamma s)) =ᶠ[𝓝 t]
        (fun s : ℝ => fderiv ℝ f (gamma s) W) := by
      filter_upwards [hNearGamma] with s hs
      have hOuter : HasFDerivAt f (fderiv ℝ f (gamma s)) (gamma s) :=
        ((hf.contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp)).hasFDerivAt
      have hComp := HasFDerivAt.comp_hasDerivAt (f := gamma) (f' := W)
        (l := f) (l' := fderiv ℝ f (gamma s)) s hOuter (hGamma s)
      simpa only [Function.comp_def] using hComp.deriv
    have hDField : HasFDerivAt (fderiv ℝ f)
        (fderiv ℝ (fderiv ℝ f) (gamma t)) (gamma t) :=
      (((hf.fderiv_of_isOpen hU (m := ∞) (by simp)).contDiffAt
        (hU.mem_nhds htU)).differentiableAt (by simp)).hasFDerivAt
    have hFieldCurve := HasFDerivAt.comp_hasDerivAt (f := gamma) (f' := W)
      (l := fderiv ℝ f) (l' := fderiv ℝ (fderiv ℝ f) (gamma t)) t hDField (hGamma t)
    have hEval := hFieldCurve.clm_apply (hasDerivAt_const t W)
    calc
      deriv (deriv (fun s : ℝ => f (z0+s • W))) t =
          deriv (fun s : ℝ => fderiv ℝ f (gamma s) W) t := hGerm.deriv_eq
      _ = fderiv ℝ (fderiv ℝ f) (z0+t • W) W W := by
        simpa only [Function.comp_def,gamma,map_zero,add_zero] using hEval.deriv
  have hFunctionLower (z : E) (hz : z ∈ closedBall z0 r) :
      (m/4)*‖z-z0‖^2 ≤ F z := by
    let W : E := z-z0
    let gamma : ℝ → E := fun t => z0+t • W
    let h : ℝ → ℝ := fun t => F (gamma t)
    have hW : ‖W‖ ≤ r := by
      have hdist : dist z z0 ≤ r := mem_closedBall.mp hz
      rw [_root_.dist_eq_norm_sub] at hdist
      simpa only [W] using hdist
    have hGamma (t : ℝ) : HasDerivAt gamma W t := by
      simpa only [gamma,one_smul] using
        ((hasDerivAt_id' t).smul_const W).const_add z0
    have hSegment (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : gamma t ∈ closedBall z0 r := by
      apply mem_closedBall.mpr
      have hAbs : |t| = t := abs_of_nonneg ht.1
      have hNorm : ‖t • W‖ ≤ r := by
        rw [norm_smul,Real.norm_eq_abs,hAbs]
        exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg W)).trans (by
          simpa only [one_mul] using hW)
      rw [_root_.dist_eq_norm_sub]
      simpa only [gamma,add_sub_cancel_left] using hNorm
    have hMaps : MapsTo gamma (Icc (0 : ℝ) 1) U := fun t ht =>
      (hClosedRoom (gamma t) (hSegment t ht)).1
    have hGammaSmooth : ContDiff ℝ ∞ gamma :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    have hIcc : ContDiffOn ℝ 2 h (Icc (0 : ℝ) 1) :=
      (hF.comp hGammaSmooth.contDiffOn hMaps).of_le (by norm_num)
    have hSmoothCurve : ContDiffOn ℝ 2 h (uIcc (0 : ℝ) 1) := by
      simpa only [uIcc_of_le zero_le_one] using hIcc
    have hZero : h 0 = 0 := by
      simpa only [h,gamma,zero_smul,add_zero] using hFzero
    have hOuter0 : HasFDerivAt F (fderiv ℝ F z0) (gamma 0) := by
      have hAt : HasFDerivAt F (fderiv ℝ F z0) z0 :=
        ((hF.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)).hasFDerivAt
      simpa only [gamma,zero_smul,add_zero] using hAt
    have hHasZero : HasDerivAt h 0 0 := by
      have hComp := HasFDerivAt.comp_hasDerivAt (f := gamma) (f' := W)
        (l := F) (l' := fderiv ℝ F z0) 0 hOuter0 (hGamma 0)
      simpa only [h,Function.comp_def,hDFzero,ContinuousLinearMap.zero_apply] using hComp
    have hWithinZero : derivWithin h (uIcc (0 : ℝ) 1) 0 = 0 := by
      have hUnique : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) 0 :=
        (uniqueDiffOn_Icc zero_lt_one) 0 ⟨le_rfl,zero_le_one⟩
      have hWithin := hHasZero.hasDerivWithinAt.derivWithin hUnique
      simpa only [uIcc_of_le zero_le_one] using hWithin
    have hTaylorZero : taylorWithinEval h 1 (uIcc (0 : ℝ) 1) 0 1 = 0 := by
      rw [taylorWithinEval_succ]
      simp only [Nat.zero_add,Nat.cast_zero,Nat.cast_one,Nat.factorial_zero,
        zero_add,one_mul,inv_one,sub_zero,pow_one,one_smul]
      rw [taylor_within_zero_eval,iteratedDerivWithin_one,hWithinZero,hZero]
      norm_num
    obtain ⟨t,ht,hTaylor⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := h) (x₀ := (0 : ℝ)) (x := (1 : ℝ)) (n := 1) (by norm_num) hSmoothCurve
    have ht01 : t ∈ Ioo (0 : ℝ) 1 := by
      simpa only [uIoo_of_lt zero_lt_one] using ht
    have hPoint := hSegment t ⟨ht01.1.le,ht01.2.le⟩
    have hSecondAt : iteratedDeriv 2 h t =
        fderiv ℝ (fderiv ℝ F) (gamma t) W W := by
      simpa only [h,gamma,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using
        curveSecond F hF W t (hMaps ⟨ht01.1.le,ht01.2.le⟩)
    have hOne : h 1 = F z := by
      change F (z0+(1 : ℝ) • W) = F z
      congr 1
      dsimp only [W]
      rw [one_smul]
      abel
    have hTaylorF : F z = fderiv ℝ (fderiv ℝ F) (gamma t) W W / 2 := by
      rw [hOne,hTaylorZero,hSecondAt] at hTaylor
      norm_num at hTaylor
      exact hTaylor
    have hLower := hHessianLower (gamma t) hPoint W
    change (m/4)*‖W‖^2 ≤ F z
    linarith only [hLower,hTaylorF]
  let c : ℝ := m/8
  have hc : 0 < c := div_pos hm (by norm_num)
  refine ⟨theta1,theta2,c,r,hSmooth1,hSmooth2,hZero1,hZero2,hFirst1,hFirst2,
    hFormula1,hFormula2,hHess1,hHess2,hPD1,hPD2,hG1,hG2,hUnit1,hUnit2,hc,hr,?_,?_,?_⟩
  · intro z hz
    exact (hClosedRoom z hz).1
  · intro z hz
    have hN1 : ‖z.1-x0‖ ≤ ‖z-z0‖ := norm_fst_le (z-z0)
    have hN2 : ‖z.2-y0‖ ≤ ‖z-z0‖ := norm_snd_le (z-z0)
    have hS1 := mul_nonneg (sub_nonneg.mpr hN1)
      (add_nonneg (norm_nonneg (z-z0)) (norm_nonneg (z.1-x0)))
    have hS2 := mul_nonneg (sub_nonneg.mpr hN2)
      (add_nonneg (norm_nonneg (z-z0)) (norm_nonneg (z.2-y0)))
    have hSquares : ‖z.1-x0‖^2+‖z.2-y0‖^2 ≤ 2*‖z-z0‖^2 := by
      nlinarith only [hS1,hS2]
    have hCompare : c*(‖z.1-x0‖^2+‖z.2-y0‖^2) ≤ (m/4)*‖z-z0‖^2 := by
      have hMul := mul_le_mul_of_nonneg_left hSquares hc.le
      dsimp only [c] at hMul ⊢
      nlinarith only [hMul]
    have hBound := hCompare.trans (hFunctionLower z hz)
    have hFformula : F z = rho z+K*(rho z)^2/2-theta1 z.1-theta2 z.2 := by
      dsimp only [F]
      ring
    rw [hFformula] at hBound
    linarith only [hBound]
  · intro z hz
    have hFactor := (hClosedRoom z hz).2.2
    have hFactorization : rho z+K*(rho z)^2/2 = rho z*(1+K*rho z/2) := by ring
    rw [hFactorization]
    exact mul_pos_iff_of_pos_right hFactor

end OAI.AnisotropicCalderon
#print axioms OAI.AnisotropicCalderon.exists_contDiff_prescribed_metricHessian
#print axioms OAI.AnisotropicCalderon.exists_local_product_phase_gap
