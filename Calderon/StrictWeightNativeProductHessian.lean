import Calderon.StrictWeightProductHessianSeparation
import Calderon.MetricHessianQuadratic
import Calderon.MetricHessianDivergence
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Native product Hessian for a strict weight, at a single point; the
source-geometric criterion and uniformity are not part of this pointwise statement. -/
set_option autoImplicit false
noncomputable section
open Set Metric Matrix Filter Topology
open scoped InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ProductHessianSeparation
open MetricVolume

local notation "V3" => (Fin 3 → ℝ)
local notation "I6" => (Fin 3 ⊕ Fin 3)
local notation "V6" => (I6 → ℝ)
local notation "M3" => Matrix (Fin 3) (Fin 3) ℝ
local notation "M6" => Matrix I6 I6 ℝ
local notation "SA3" => selfAdjoint M3

theorem exists_prescribed_metric_forms_of_productHessian_positive
     (g1 g2 : MatrixField) (x0 y0 : R3) (rho : R3 × R3 → ℝ)
     (hrho : ContDiffAt ℝ 2 rho (x0,y0))
     (hg1 : ∀ i j, DifferentiableAt ℝ (fun x => g1 x i j) x0)
     (hg2 : ∀ i j, DifferentiableAt ℝ (fun y => g2 y i j) y0)
     (hp1 : (g1 x0).PosDef) (hp2 : (g2 y0).PosDef)
     (hs1 : ∀ᶠ x in 𝓝 x0, (g1 x).IsHermitian)
     (hs2 : ∀ᶠ y in 𝓝 y0, (g2 y).IsHermitian) :
     let ell : R3 × R3 →L[ℝ] ℝ := fderiv ℝ rho (x0,y0)
     let ell1 : R3 →L[ℝ] ℝ := ell.comp (ContinuousLinearMap.inl ℝ R3 R3)
     let ell2 : R3 →L[ℝ] ℝ := ell.comp (ContinuousLinearMap.inr ℝ R3 R3)
     let M1 : R3 →L[ℝ] R3 := MetricOperator.metricOperatorField g1 x0
     let M2 : R3 →L[ℝ] R3 := MetricOperator.metricOperatorField g2 y0
     let Gamma1 : R3 →L[ℝ] R3 →L[ℝ] R3 := ConnectionError.coordinateConnectionField
       (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g1))
       (MetricOperator.metricOperatorField g1) x0
     let Gamma2 : R3 →L[ℝ] R3 →L[ℝ] R3 := ConnectionError.coordinateConnectionField
       (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g2))
       (MetricOperator.metricOperatorField g2) y0
     let b1 : R3 := MetricOperator.matrixOperatorMap ((g1 x0)⁻¹)
       (WithLp.toLp 2 (fun i : Fin 3 => ell1 (coordinateVector i)))
     let b2 : R3 := MetricOperator.matrixOperatorMap ((g2 y0)⁻¹)
       (WithLp.toLp 2 (fun i : Fin 3 => ell2 (coordinateVector i)))
     let a1 : R3 := (⟪M1 b1,b1⟫_ℝ)⁻¹ • b1
     let a2 : R3 := (⟪M2 b2,b2⟫_ℝ)⁻¹ • b2
     let H : (R3 × R3) → (R3 × R3) → ℝ := fun X Y =>
       fderiv ℝ (fderiv ℝ rho) (x0,y0) X Y -
         ell (Gamma1 X.1 Y.1,Gamma2 X.2 Y.2)
     ell1 ≠ 0 → ell2 ≠ 0 →
     (∀ v1 v2 : R3,
       ⟪M1 v1,a1⟫_ℝ = 0 → ⟪M1 v1,v1⟫_ℝ = ⟪M1 a1,a1⟫_ℝ →
       ⟪M2 v2,a2⟫_ℝ = 0 → ⟪M2 v2,v2⟫_ℝ = ⟪M2 a2,a2⟫_ℝ →
       0 < H (a1,-a2) (a1,-a2) + H (v1,v2) (v1,v2)) →
     ∃ (P1 P2 : R3 →L[ℝ] R3 →L[ℝ] ℝ) (K : ℝ),
       (∀ X Y : R3, P1 X Y = P1 Y X) ∧
       (∀ X Y : R3, P2 X Y = P2 Y X) ∧ 0 < K ∧
       (∀ v : R3, ⟪M1 v,a1⟫_ℝ = 0 → ⟪M1 v,v⟫_ℝ = ⟪M1 a1,a1⟫_ℝ →
         0 < P1 a1 a1 + P1 v v) ∧
       (∀ v : R3, ⟪M2 v,a2⟫_ℝ = 0 → ⟪M2 v,v⟫_ℝ = ⟪M2 a2,a2⟫_ℝ →
         0 < P2 a2 a2 + P2 v v) ∧
       (∀ W : R3 × R3, W ≠ 0 →
         0 < fderiv ℝ (fderiv ℝ rho) (x0,y0) W W -
           ell (Gamma1 W.1 W.1,Gamma2 W.2 W.2) + K*(ell W)^2 -
             P1 W.1 W.1 - P2 W.2 W.2) := by
  classical
  intro ell ell1 ell2 M1 M2 Gamma1 Gamma2 b1 b2 a1 a2 H
  intro hEll1 hEll2 hsource
  let c1 : V3 := fun j => ell1 (coordinateVector j)
  let c2 : V3 := fun j => ell2 (coordinateVector j)
  let N1 : ℝ := ⟪M1 b1,b1⟫_ℝ
  let N2 : ℝ := ⟪M2 b2,b2⟫_ℝ
  have hCovector (F : R3 →L[ℝ] ℝ) (X : R3) :
      F X = dotProduct (fun j => F (coordinateVector j)) (X : V3) := by
    rw [MetricVolume.covector_coordinate_sum]
    exact dotProduct_comm _ _
  have hMetric (G : M3) (X Y : R3) :
      ⟪MetricOperator.matrixOperatorMap G X,Y⟫_ℝ =
        dotProduct (Y : V3) (G *ᵥ (X : V3)) := by
    change ⟪G.toEuclideanLin X,Y⟫_ℝ = _
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,Pi.star_apply,star_trivial,
      Matrix.toEuclideanLin,Matrix.toLpLin_apply,WithLp.ofLp_toLp]
  have hFactor (G : M3) (hG : G.PosDef) (F : R3 →L[ℝ] ℝ) (hF : F ≠ 0) :
      let b : R3 := MetricOperator.matrixOperatorMap G⁻¹
        (WithLp.toLp 2 (fun j : Fin 3 => F (coordinateVector j)))
      let n : ℝ := ⟪MetricOperator.matrixOperatorMap G b,b⟫_ℝ
      let a : R3 := n⁻¹ • b
      0 < n ∧ F a = 1 ∧ ∀ X : R3,
        ⟪MetricOperator.matrixOperatorMap G X,a⟫_ℝ = n⁻¹ * F X := by
    intro b n a
    let c : V3 := fun j => F (coordinateVector j)
    have hc : c ≠ 0 := by
      intro hz
      apply hF
      ext X
      rw [hCovector]
      change dotProduct c (X : V3) = 0
      rw [hz,zero_dotProduct]
    have hGB : ∀ X : R3,
        MetricOperator.matrixOperatorMap G (MetricOperator.matrixOperatorMap G⁻¹ X) = X := by
      have hmat : G*G⁻¹ = 1 :=
        Matrix.mul_nonsing_inv G ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit)
      have hop : MetricOperator.matrixOperatorMap G * MetricOperator.matrixOperatorMap G⁻¹ = 1 := by
        change MetricOperator.matrixOperatorAlgEquiv G *
          MetricOperator.matrixOperatorAlgEquiv G⁻¹ = 1
        rw [← map_mul,hmat,map_one]
      intro X
      change (MetricOperator.matrixOperatorMap G * MetricOperator.matrixOperatorMap G⁻¹) X = X
      rw [hop]
      rfl
    have hb : b ≠ 0 := by
      intro hb0
      have he := hGB (WithLp.toLp 2 c)
      change MetricOperator.matrixOperatorMap G b = WithLp.toLp 2 c at he
      rw [hb0,map_zero] at he
      apply hc
      ext j
      exact (congrArg (fun X : R3 => X j) he).symm
    have hbCoord : (b : V3) ≠ 0 := by
      intro hz
      apply hb
      ext j
      exact congrFun hz j
    have hn : 0 < n := by
      change 0 < ⟪MetricOperator.matrixOperatorMap G b,b⟫_ℝ
      rw [hMetric]
      simpa only [star_trivial] using hG.dotProduct_mulVec_pos hbCoord
    have hGradient (X : R3) : ⟪MetricOperator.matrixOperatorMap G b,X⟫_ℝ = F X := by
      change ⟪MetricOperator.matrixOperatorMap G
        (MetricOperator.matrixOperatorMap G⁻¹ (WithLp.toLp 2 c)),X⟫_ℝ = _
      rw [hGB,MetricVolume.covector_coordinate_sum F X]
      simp only [EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,
        Pi.star_apply,star_trivial,c,dotProduct]
    have hNorm : F b = n := (hGradient b).symm
    refine ⟨hn,?_,?_⟩
    · change F (n⁻¹ • b) = 1
      rw [map_smul,smul_eq_mul,hNorm,inv_mul_cancel₀ hn.ne']
    · intro X
      have hSym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hG.isHermitian
      have hPair : ⟪MetricOperator.matrixOperatorMap G X,b⟫_ℝ = F X := by
        change ⟪G.toEuclideanLin X,b⟫_ℝ = F X
        exact ((hSym X b).trans (real_inner_comm _ _)).trans (hGradient X)
      change ⟪MetricOperator.matrixOperatorMap G X,n⁻¹ • b⟫_ℝ = n⁻¹ * F X
      rw [inner_smul_right,hPair]
  obtain ⟨hn1,ha1,hPair1⟩ := hFactor (g1 x0) hp1 ell1 hEll1
  obtain ⟨hn2,ha2,hPair2⟩ := hFactor (g2 y0) hp2 ell2 hEll2
  change 0 < N1 at hn1
  change 0 < N2 at hn2
  change ell1 a1 = 1 at ha1
  change ell2 a2 = 1 at ha2
  change ∀ X : R3, ⟪M1 X,a1⟫_ℝ = N1⁻¹ * ell1 X at hPair1
  change ∀ X : R3, ⟪M2 X,a2⟫_ℝ = N2⁻¹ * ell2 X at hPair2
  have haCoord1 : dotProduct c1 (a1 : V3) = 1 := (hCovector ell1 a1).symm.trans ha1
  have haCoord2 : dotProduct c2 (a2 : V3) = 1 := (hCovector ell2 a2).symm.trans ha2
  have hSphere1 (X : R3) :
      (X : V3) ∈ metricTangentSphere (g1 x0) c1 (a1 : V3) ↔
        ⟪M1 X,a1⟫_ℝ = 0 ∧ ⟪M1 X,X⟫_ℝ = ⟪M1 a1,a1⟫_ℝ := by
    change (dotProduct c1 (X : V3) = 0 ∧
      dotProduct (X : V3) ((g1 x0)*ᵥ(X : V3)) =
        dotProduct (a1 : V3) ((g1 x0)*ᵥ(a1 : V3))) ↔ _
    have hXX : ⟪M1 X,X⟫_ℝ =
        dotProduct (X : V3) ((g1 x0)*ᵥ(X : V3)) := hMetric (g1 x0) X X
    have hAA : ⟪M1 a1,a1⟫_ℝ =
        dotProduct (a1 : V3) ((g1 x0)*ᵥ(a1 : V3)) := hMetric (g1 x0) a1 a1
    rw [hPair1 X,hXX,hAA,hCovector ell1 X]
    exact and_congr (by simp only [c1,mul_eq_zero,inv_ne_zero hn1.ne',false_or]) Iff.rfl
  have hSphere2 (X : R3) :
      (X : V3) ∈ metricTangentSphere (g2 y0) c2 (a2 : V3) ↔
        ⟪M2 X,a2⟫_ℝ = 0 ∧ ⟪M2 X,X⟫_ℝ = ⟪M2 a2,a2⟫_ℝ := by
    change (dotProduct c2 (X : V3) = 0 ∧
      dotProduct (X : V3) ((g2 y0)*ᵥ(X : V3)) =
        dotProduct (a2 : V3) ((g2 y0)*ᵥ(a2 : V3))) ↔ _
    have hXX : ⟪M2 X,X⟫_ℝ =
        dotProduct (X : V3) ((g2 y0)*ᵥ(X : V3)) := hMetric (g2 y0) X X
    have hAA : ⟪M2 a2,a2⟫_ℝ =
        dotProduct (a2 : V3) ((g2 y0)*ᵥ(a2 : V3)) := hMetric (g2 y0) a2 a2
    rw [hPair2 X,hXX,hAA,hCovector ell2 X]
    exact and_congr (by simp only [c2,mul_eq_zero,inv_ne_zero hn2.ne',false_or]) Iff.rfl
  have hEllPair (X Y : R3) : ell (X,Y) = ell1 X + ell2 Y :=
    (ell.comp_inl_add_comp_inr (X,Y)).symm
  let B : (R3 × R3) →L[ℝ] (R3 × R3) →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ rho) (x0,y0)
  have hHValue (X Y : R3 × R3) :
      H X Y = B X Y-ell1 (Gamma1 X.1 Y.1)-ell2 (Gamma2 X.2 Y.2) := by
    change B X Y-ell (Gamma1 X.1 Y.1,Gamma2 X.2 Y.2) = _
    rw [hEllPair]
    ring
  let HL : LinearMap.BilinForm ℝ (R3 × R3) :=
    { toFun := fun X =>
        { toFun := fun Y => B X Y-ell1 (Gamma1 X.1 Y.1)-ell2 (Gamma2 X.2 Y.2)
          map_add' := by
            intro Y Z
            change B X (Y+Z)-ell1 (Gamma1 X.1 (Y.1+Z.1))-
              ell2 (Gamma2 X.2 (Y.2+Z.2)) =
                (B X Y-ell1 (Gamma1 X.1 Y.1)-ell2 (Gamma2 X.2 Y.2))+
                (B X Z-ell1 (Gamma1 X.1 Z.1)-ell2 (Gamma2 X.2 Z.2))
            simp only [map_add]
            ring
          map_smul' := by
            intro t Y
            change B X (t • Y)-ell1 (Gamma1 X.1 (t • Y.1))-
              ell2 (Gamma2 X.2 (t • Y.2)) =
                t*(B X Y-ell1 (Gamma1 X.1 Y.1)-ell2 (Gamma2 X.2 Y.2))
            simp only [map_smul,smul_eq_mul]
            ring }
      map_add' := by
        intro X Y
        apply LinearMap.ext
        intro Z
        change B (X+Y) Z-ell1 (Gamma1 (X.1+Y.1) Z.1)-
          ell2 (Gamma2 (X.2+Y.2) Z.2) =
            (B X Z-ell1 (Gamma1 X.1 Z.1)-ell2 (Gamma2 X.2 Z.2))+
            (B Y Z-ell1 (Gamma1 Y.1 Z.1)-ell2 (Gamma2 Y.2 Z.2))
        simp only [map_add,ContinuousLinearMap.add_apply]
        ring
      map_smul' := by
        intro t X
        apply LinearMap.ext
        intro Y
        change B (t • X) Y-ell1 (Gamma1 (t • X.1) Y.1)-
          ell2 (Gamma2 (t • X.2) Y.2) =
            t*(B X Y-ell1 (Gamma1 X.1 Y.1)-ell2 (Gamma2 X.2 Y.2))
        simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
        ring }
  have hHL (X Y : R3 × R3) : HL X Y = H X Y := (hHValue X Y).symm
  have hHSym (X Y : R3 × R3) : H X Y = H Y X := by
    change B X Y-ell (Gamma1 X.1 Y.1,Gamma2 X.2 Y.2) =
      B Y X-ell (Gamma1 Y.1 X.1,Gamma2 Y.2 X.2)
    rw [(hrho.isSymmSndFDerivAt (by simp)).eq X Y]
    rw [MetricVolume.actualMetricConnection_symmetric_local g1 x0 hg1 hs1,
      MetricVolume.actualMetricConnection_symmetric_local g2 y0 hg2 hs2]
  let basis : Module.Basis (Fin 3) ℝ R3 := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let basisE : Module.Basis I6 ℝ (R3 × R3) := basis.prod basis
  let coord : R3 × R3 → V6 := fun X i => basisE.repr X i
  have hBasisRepr (X : R3) (j : Fin 3) : basis.repr X j = X j := by
    simp only [basis,OrthonormalBasis.coe_toBasis_repr_apply,EuclideanSpace.basisFun_repr]
  have hCoordLeft (X : R3 × R3) (j : Fin 3) : coord X (Sum.inl j) = X.1 j := by
    change (basis.prod basis).repr X (Sum.inl j) = _
    rw [Module.Basis.prod_repr_inl,hBasisRepr]
  have hCoordRight (X : R3 × R3) (j : Fin 3) : coord X (Sum.inr j) = X.2 j := by
    change (basis.prod basis).repr X (Sum.inr j) = _
    rw [Module.Basis.prod_repr_inr,hBasisRepr]
  have hCoord (X : R3 × R3) : coord X = Sum.elim (X.1 : V3) (X.2 : V3) := by
    ext j
    cases j with
    | inl j => exact hCoordLeft X j
    | inr j => exact hCoordRight X j
  have hCoordNe (X : R3 × R3) (hX : X ≠ 0) : coord X ≠ 0 := by
    intro hz
    apply hX
    apply Prod.ext
    · ext j
      exact (hCoordLeft X j).symm.trans (congrFun hz (Sum.inl j))
    · ext j
      exact (hCoordRight X j).symm.trans (congrFun hz (Sum.inr j))
  let H0 : M6 := LinearMap.BilinForm.toMatrix basisE HL
  have hHMatrix (X Y : R3 × R3) :
      dotProduct (coord X) (H0*ᵥcoord Y) = H X Y := by
    exact (LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec basisE HL X Y).symm.trans
      (hHL X Y)
  have hH0 : H0.IsHermitian := by
    ext i j
    simp only [H0,Matrix.conjTranspose_apply,star_trivial,LinearMap.BilinForm.toMatrix_apply,hHL]
    exact hHSym _ _
  let c : V6 := Sum.elim c1 c2
  have hEllCoord (X : R3 × R3) : dotProduct c (coord X) = ell X := by
    change dotProduct (Sum.elim c1 c2) (coord X) = ell X
    rw [hCoord,sumElim_dotProduct_sumElim]
    rw [← hCovector ell1 X.1,← hCovector ell2 X.2]
    exact (hEllPair X.1 X.2).symm
  have hFiniteSource : ∀ v1 ∈ metricTangentSphere (g1 x0) c1 (a1 : V3),
      ∀ v2 ∈ metricTangentSphere (g2 y0) c2 (a2 : V3),
      0 < dotProduct (Sum.elim (a1 : V3) (-(a2 : V3)))
        (H0*ᵥSum.elim (a1 : V3) (-(a2 : V3))) +
        dotProduct (Sum.elim v1 v2) (H0*ᵥSum.elim v1 v2) := by
    intro v1 hv1 v2 hv2
    let V1 : R3 := WithLp.toLp 2 v1
    let V2 : R3 := WithLp.toLp 2 v2
    have hv1' := (hSphere1 V1).mp hv1
    have hv2' := (hSphere2 V2).mp hv2
    have hs := hsource V1 V2 hv1'.1 hv1'.2 hv2'.1 hv2'.2
    have hA : coord (a1,-a2) = Sum.elim (a1 : V3) (-(a2 : V3)) := by
      rw [hCoord (a1,-a2)]
      rfl
    have hV : coord (V1,V2) = Sum.elim v1 v2 := by
      rw [hCoord (V1,V2)]
    rw [← hA,← hV,hHMatrix (a1,-a2) (a1,-a2),hHMatrix (V1,V2) (V1,V2)]
    exact hs
  obtain ⟨Pmat1,Pmat2,K,hK,hPmat1,hPmat2,hPD⟩ :=
    exists_strict_block_forms_of_tangentSphere_positive
      (g1 x0) (g2 y0) hp1 hp2 c1 c2 (a1 : V3) (a2 : V3)
      haCoord1 haCoord2 H0 hH0 hFiniteSource
  let toCL : (R3 →ₗ[ℝ] ℝ) →ₗ[ℝ] (R3 →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap : (R3 →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (R3 →L[ℝ] ℝ)).toLinearMap
  let nativeForm : M3 → R3 →L[ℝ] R3 →L[ℝ] ℝ := fun P =>
    LinearMap.toContinuousLinearMap (toCL.comp (Matrix.toBilin basis P))
  have hNativeValue (P : M3) (X Y : R3) :
      nativeForm P X Y = dotProduct (X : V3) (P*ᵥ(Y : V3)) := by
    change Matrix.toBilin basis P X Y = _
    rw [Matrix.toBilin_apply]
    simp only [hBasisRepr,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
  have hNativeSym (P : SA3) (X Y : R3) :
      nativeForm (P : M3) X Y = nativeForm (P : M3) Y X := by
    rw [hNativeValue,hNativeValue]
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hji : (P : M3) j i = (P : M3) i j := by
      have hPH : (P : M3)ᴴ = (P : M3) := P.2
      simpa only [Matrix.conjTranspose_apply,star_trivial] using
        congrArg (fun A : M3 => A i j) hPH
    rw [hji]
    ring
  refine ⟨nativeForm (Pmat1 : M3),nativeForm (Pmat2 : M3),K,
    hNativeSym Pmat1,hNativeSym Pmat2,hK,?_,?_,?_⟩
  · intro v hv hn
    have hmem := (hSphere1 v).mpr ⟨hv,hn⟩
    simpa only [hNativeValue] using hPmat1 (v : V3) hmem
  · intro v hv hn
    have hmem := (hSphere2 v).mpr ⟨hv,hn⟩
    simpa only [hNativeValue] using hPmat2 (v : V3) hmem
  · intro W hW
    have hcW := hCoordNe W hW
    have hPositive := hPD.dotProduct_mulVec_pos hcW
    simp only [star_trivial] at hPositive
    have hRank (v w z : V6) :
        Matrix.vecMulVec v w*ᵥz = dotProduct w z • v := by
      ext i
      simp only [Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hPenalty : dotProduct (coord W) ((K • Matrix.vecMulVec c c)*ᵥcoord W) =
        K*(ell W)^2 := by
      rw [Matrix.smul_mulVec,hRank,dotProduct_smul,dotProduct_smul]
      rw [dotProduct_comm (coord W) c]
      simp only [hEllCoord,smul_eq_mul]
      ring
    have hBlock : dotProduct (coord W)
        ((Matrix.fromBlocks (Pmat1 : M3) 0 0 (Pmat2 : M3))*ᵥcoord W) =
          nativeForm (Pmat1 : M3) W.1 W.1 + nativeForm (Pmat2 : M3) W.2 W.2 := by
      rw [hNativeValue (Pmat1 : M3) W.1 W.1,hNativeValue (Pmat2 : M3) W.2 W.2,hCoord W]
      simp only [dotProduct,Matrix.mulVec,Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply,zero_mul,Finset.sum_const_zero,add_zero,zero_add,
        Sum.elim_inl,Sum.elim_inr,Finset.mul_sum,Finset.sum_add_distrib]
    have hPositive' : 0 < H W W+K*(ell W)^2-
        (nativeForm (Pmat1 : M3) W.1 W.1+nativeForm (Pmat2 : M3) W.2 W.2) := by
      change 0 < dotProduct (coord W)
        ((H0+K • Matrix.vecMulVec c c-Matrix.fromBlocks (Pmat1 : M3) 0 0
          (Pmat2 : M3))*ᵥcoord W) at hPositive
      simpa only [Matrix.sub_mulVec,Matrix.add_mulVec,dotProduct_sub,dotProduct_add,
        hHMatrix W W,hPenalty,hBlock] using hPositive
    change 0 < H W W+K*(ell W)^2-nativeForm (Pmat1 : M3) W.1 W.1-
      nativeForm (Pmat2 : M3) W.2 W.2
    linarith only [hPositive']

end OAI.AnisotropicCalderon.ProductHessianSeparation

#print axioms OAI.AnisotropicCalderon.ProductHessianSeparation.exists_prescribed_metric_forms_of_productHessian_positive
