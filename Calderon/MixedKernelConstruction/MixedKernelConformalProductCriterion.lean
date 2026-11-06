import Calderon.MixedKernelConstruction.MixedKernelProductPhases
import Calderon.MixedKernelConstruction.MixedKernelConformalCharacteristicPair
import Calderon.MetricHessianDivergence
import Calderon.PositiveConformalMetric
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open scoped InnerProductSpace
open MetricOperator MetricVolume ConnectionError ConformalDepth

/-- The literal covector-to-vector map used in the native product criterion. -/
def metricCovectorGradient (G : Matrix (Fin 3) (Fin 3) ℝ)
    (ell : R3 →L[ℝ] ℝ) : R3 :=
  matrixOperatorMap G⁻¹ (WithLp.toLp 2 (fun i : Fin 3 => ell (coordinateVector i)))

/-- The native normal, normalized by its squared metric length. -/
def normalizedMetricCovector (G : Matrix (Fin 3) (Fin 3) ℝ)
    (ell : R3 →L[ℝ] ℝ) : R3 :=
  (⟪matrixOperatorMap G (metricCovectorGradient G ell),metricCovectorGradient G ell⟫_ℝ)⁻¹ •
    metricCovectorGradient G ell

/-- Actual matrix inversion gives the native normal's positivity, normalization and duality. -/
theorem normalizedMetricCovector_data (G : Matrix (Fin 3) (Fin 3) ℝ)
    (hG : G.PosDef) (ell : R3 →L[ℝ] ℝ) (hell : ell ≠ 0) :
    let b := metricCovectorGradient G ell
    let N := ⟪matrixOperatorMap G b,b⟫_ℝ
    let a := normalizedMetricCovector G ell
    0 < N ∧ ell a = 1 ∧ 0 < ⟪matrixOperatorMap G a,a⟫_ℝ ∧
      ∀ X : R3, ⟪matrixOperatorMap G a,X⟫_ℝ = ⟪matrixOperatorMap G a,a⟫_ℝ * ell X := by
  intro b N a
  let c : Fin 3 → ℝ := fun j => ell (coordinateVector j)
  have hCovector (X : R3) : ell X = dotProduct c (X : Fin 3 → ℝ) := by
    rw [covector_coordinate_sum]
    exact dotProduct_comm _ _
  have hMetric (A : Matrix (Fin 3) (Fin 3) ℝ) (X Y : R3) :
      ⟪matrixOperatorMap A X,Y⟫_ℝ =
        dotProduct (Y : Fin 3 → ℝ) (Matrix.mulVec A (X : Fin 3 → ℝ)) := by
    change ⟪A.toEuclideanLin X,Y⟫_ℝ = _
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,Pi.star_apply,star_trivial,
      Matrix.toEuclideanLin,Matrix.toLpLin_apply,WithLp.ofLp_toLp]
  have hc : c ≠ 0 := by
    intro hz
    apply hell
    ext X
    rw [hCovector]
    change dotProduct c (X : Fin 3 → ℝ) = 0
    rw [hz,zero_dotProduct]
  have hGB (X : R3) : matrixOperatorMap G (matrixOperatorMap G⁻¹ X) = X := by
    have hmat : G*G⁻¹ = 1 :=
      Matrix.mul_nonsing_inv G ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit)
    have hop : matrixOperatorMap G * matrixOperatorMap G⁻¹ = 1 := by
      change matrixOperatorAlgEquiv G * matrixOperatorAlgEquiv G⁻¹ = 1
      rw [← map_mul,hmat,map_one]
    change (matrixOperatorMap G * matrixOperatorMap G⁻¹) X = X
    rw [hop]
    rfl
  have hb : b ≠ 0 := by
    intro hb0
    have he := hGB (WithLp.toLp 2 c)
    change matrixOperatorMap G b = WithLp.toLp 2 c at he
    rw [hb0,map_zero] at he
    apply hc
    ext j
    exact (congrArg (fun X : R3 => X j) he).symm
  have hbCoord : (b : Fin 3 → ℝ) ≠ 0 := by
    intro hz
    apply hb
    ext j
    exact congrFun hz j
  have hN : 0 < N := by
    change 0 < ⟪matrixOperatorMap G b,b⟫_ℝ
    rw [hMetric]
    simpa only [star_trivial] using hG.dotProduct_mulVec_pos hbCoord
  have hGradient (X : R3) : ⟪matrixOperatorMap G b,X⟫_ℝ = ell X := by
    change ⟪matrixOperatorMap G (matrixOperatorMap G⁻¹ (WithLp.toLp 2 c)),X⟫_ℝ = _
    rw [hGB,covector_coordinate_sum ell X]
    simp only [EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,
      Pi.star_apply,star_trivial,c,dotProduct]
  have hNorm : ell b = N := (hGradient b).symm
  have ha : ell a = 1 := by
    change ell (N⁻¹ • b) = 1
    rw [map_smul,smul_eq_mul,hNorm,inv_mul_cancel₀ hN.ne']
  have hPair (X : R3) : ⟪matrixOperatorMap G a,X⟫_ℝ = N⁻¹ * ell X := by
    change ⟪matrixOperatorMap G (N⁻¹ • b),X⟫_ℝ = _
    rw [map_smul,real_inner_smul_left,hGradient]
  have hAA : ⟪matrixOperatorMap G a,a⟫_ℝ = N⁻¹ := by
    rw [hPair,ha,mul_one]
  exact ⟨hN,ha,by rw [hAA];exact inv_pos.mpr hN,fun X => by rw [hAA];exact hPair X⟩

/-- Positive conformal rescaling preserves the literal native normalized normal. -/
theorem normalizedMetricCovector_smul (G : Matrix (Fin 3) (Fin 3) ℝ)
    (hG : G.PosDef) (ell : R3 →L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0) :
    normalizedMetricCovector (c • G) ell = normalizedMetricCovector G ell := by
  letI : Invertible c := invertibleOfNonzero hc
  have hInv : (c • G)⁻¹ = c⁻¹ • G⁻¹ := by
    simpa only [invOf_eq_inv] using Matrix.inv_smul G c
      ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit)
  have hb : metricCovectorGradient (c • G) ell = c⁻¹ • metricCovectorGradient G ell := by
    simp only [metricCovectorGradient,hInv,map_smul,ContinuousLinearMap.smul_apply]
  have hMb : matrixOperatorMap (c • G) (metricCovectorGradient (c • G) ell) =
      matrixOperatorMap G (metricCovectorGradient G ell) := by
    rw [hb,map_smul]
    simp only [ContinuousLinearMap.smul_apply,map_smul,smul_smul,inv_mul_cancel₀ hc,one_smul]
  have hN :
      ⟪matrixOperatorMap (c • G) (metricCovectorGradient (c • G) ell),
        metricCovectorGradient (c • G) ell⟫_ℝ =
      c⁻¹ * ⟪matrixOperatorMap G (metricCovectorGradient G ell),metricCovectorGradient G ell⟫_ℝ := by
    rw [hMb,hb,real_inner_smul_right]
  unfold normalizedMetricCovector
  rw [hN,hb,mul_inv_rev,inv_inv,smul_smul]
  congr 1
  rw [mul_assoc,mul_inv_cancel₀ hc,mul_one]

/-- The actual connection of a positive scalar multiple has the conformal correction. -/
theorem metric_connection_smul_eq_conformal (g : MatrixField)
    (c : R3 → ℝ) (x : R3) (hgd : DifferentiableAt ℝ (metricOperatorField g) x)
    (hgp : (g x).PosDef) (dc : R3 →L[ℝ] ℝ)
    (hc : HasFDerivAt c dc x) (hcx : 0 < c x) (X Y : R3) :
    coordinateConnectionField
      (inverseMetricField (metricOperatorField (fun y => c y • g y)))
      (metricOperatorField (fun y => c y • g y)) x X Y =
    conformalConnection (-(1/2 : ℝ))
      (inverseMetricField (metricOperatorField g) x) (metricOperatorField g x)
      (fderiv ℝ (metricOperatorField g) x) ((c x)⁻¹ • dc) X Y := by
  let M := metricOperatorField g
  let Q := inverseMetricField M
  have hM : HasFDerivAt M (fderiv ℝ M x) x := hgd.hasFDerivAt
  have hScaled : metricOperatorField (fun y => c y • g y) = fun y => c y • M y := by
    funext y
    exact map_smul matrixOperatorMap (c y) (g y)
  have hD : fderiv ℝ (metricOperatorField (fun y => c y • g y)) x =
      conformalMetricDerivative (c x) (-(1/2 : ℝ)) (M x)
        (fderiv ℝ M x) ((c x)⁻¹ • dc) := by
    rw [hScaled]
    change fderiv ℝ (c • M) x = _
    rw [(hc.smul hM).fderiv]
    have hf : -2 * (-(1/2 : ℝ)) * c x = c x := by ring
    simp only [conformalMetricDerivative,hf,smul_smul,mul_inv_cancel₀ hcx.ne',one_smul]
  have hInv : (c x • g x)⁻¹ = (c x)⁻¹ • (g x)⁻¹ := by
    letI : Invertible (c x) := invertibleOfNonzero hcx.ne'
    simpa only [invOf_eq_inv] using Matrix.inv_smul (g x) (c x)
      ((Matrix.isUnit_iff_isUnit_det (g x)).mp hgp.isUnit)
  have hQ : inverseMetricField (metricOperatorField (fun y => c y • g y)) x =
      (c x)⁻¹ • Q x := by
    rw [inverseMetricField_eq_matrix_inverse_of_posDef _ x (hgp.smul hcx),hInv]
    change matrixOperatorMap ((c x)⁻¹ • (g x)⁻¹) =
      (c x)⁻¹ • inverseMetricField (metricOperatorField g) x
    rw [inverseMetricField_eq_matrix_inverse_of_posDef g x hgp,map_smul]
  have hunit : IsUnit (M x) := hgp.isUnit.map matrixOperatorAlgEquiv.toMonoidHom
  have hQM (Z : R3) : Q x (M x Z) = Z := by
    exact congrArg (fun A : R3 →L[ℝ] R3 => A Z) (Ring.inverse_mul_cancel (M x) hunit)
  have hMQ (Z : R3) : M x (Q x Z) = Z := by
    exact congrArg (fun A : R3 →L[ℝ] R3 => A Z) (Ring.mul_inverse_cancel (M x) hunit)
  have hsym (X Y : R3) : ⟪M x X,Y⟫_ℝ = ⟪M x Y,X⟫_ℝ := by
    have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hgp.isHermitian
    exact (hs X Y).trans (real_inner_comm _ _)
  rw [coordinateConnectionField_apply,hQ,hD]
  exact coordinateConnection_conformal (c x) (-(1/2 : ℝ)) (Q x) (M x)
    (fderiv ℝ M x) ((c x)⁻¹ • dc) hcx.ne'
    hQM hMQ hsym X Y

/-- The conformal correction cancels for the literal native normal and actual tangent sphere. -/
theorem native_metric_characteristic_connection_cancellation
    (g : MatrixField) (c : R3 → ℝ) (x : R3)
    (hgd : DifferentiableAt ℝ (metricOperatorField g) x) (hgp : (g x).PosDef)
    (dc ell : R3 →L[ℝ] ℝ) (hc : HasFDerivAt c dc x) (hcx : 0 < c x)
    (hell : ell ≠ 0) (v : R3)
    (horth : ⟪metricOperatorField g x v,normalizedMetricCovector (g x) ell⟫_ℝ = 0)
    (hequal : ⟪metricOperatorField g x v,v⟫_ℝ =
      ⟪metricOperatorField g x (normalizedMetricCovector (g x) ell),
        normalizedMetricCovector (g x) ell⟫_ℝ) :
    let a := normalizedMetricCovector (g x) ell
    let G := coordinateConnectionField
      (inverseMetricField (metricOperatorField g)) (metricOperatorField g) x
    let G' := coordinateConnectionField
      (inverseMetricField (metricOperatorField (fun y => c y • g y)))
      (metricOperatorField (fun y => c y • g y)) x
    ell (G' a a) + ell (G' v v) = ell (G a a) + ell (G v v) := by
  intro a G G'
  obtain ⟨hN,ha,hAA,hdual⟩ := normalizedMetricCovector_data (g x) hgp ell hell
  have hsym (X Y : R3) : ⟪metricOperatorField g x X,Y⟫_ℝ = ⟪metricOperatorField g x Y,X⟫_ℝ := by
    have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hgp.isHermitian
    exact (hs X Y).trans (real_inner_comm _ _)
  have hv : ell v = 0 := by
    have hh := hdual v
    change ⟪metricOperatorField g x a,v⟫_ℝ = ⟪metricOperatorField g x a,a⟫_ℝ * ell v at hh
    have ho : ⟪metricOperatorField g x v,a⟫_ℝ = 0 := horth
    rw [← hsym v a,ho] at hh
    change 0 = ⟪metricOperatorField g x a,a⟫_ℝ * ell v at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hAA.ne'
  change ell (coordinateConnectionField _ _ x a a) +
      ell (coordinateConnectionField _ _ x v v) =
    ell (coordinateConnectionField _ _ x a a) + ell (coordinateConnectionField _ _ x v v)
  rw [metric_connection_smul_eq_conformal g c x hgd hgp dc hc hcx,
      metric_connection_smul_eq_conformal g c x hgd hgp dc hc hcx,
      coordinateConnectionField_apply,coordinateConnectionField_apply]
  have hunit : IsUnit (metricOperatorField g x) := hgp.isUnit.map matrixOperatorAlgEquiv.toMonoidHom
  have hMQ (Z : R3) : metricOperatorField g x (inverseMetricField (metricOperatorField g) x Z) = Z := by
    exact congrArg (fun A : R3 →L[ℝ] R3 => A Z) (Ring.mul_inverse_cancel _ hunit)
  exact conformal_connection_characteristic_pair_cancellation (-(1/2 : ℝ))
    (inverseMetricField (metricOperatorField g) x) (metricOperatorField g x)
    (fderiv ℝ (metricOperatorField g) x) ((c x)⁻¹ • dc) ell a v
    hMQ hsym hdual ha hv hequal

/-- The literal native product-Hessian test is invariant under positive differentiable
conformal changes in its two metric factors. No Hessian correspondence is assumed. -/
theorem productHessianStrictAt_smul
    (g1 g2 : MatrixField) (c1 c2 : R3 → ℝ) (x y : R3) (rho : R3 × R3 → ℝ)
    (hgd1 : DifferentiableAt ℝ (metricOperatorField g1) x) (hgp1 : (g1 x).PosDef)
    (hgd2 : DifferentiableAt ℝ (metricOperatorField g2) y) (hgp2 : (g2 y).PosDef)
    (hc1 : DifferentiableAt ℝ c1 x) (hc2 : DifferentiableAt ℝ c2 y)
    (hcx : 0 < c1 x) (hcy : 0 < c2 y) :
    ProductHessianStrictAt (fun z => c1 z • g1 z) (fun z => c2 z • g2 z) x y rho ↔
      ProductHessianStrictAt g1 g2 x y rho := by
  let ell := fderiv ℝ rho (x,y)
  let ell1 := ell.comp (ContinuousLinearMap.inl ℝ R3 R3)
  let ell2 := ell.comp (ContinuousLinearMap.inr ℝ R3 R3)
  let a1 := normalizedMetricCovector (g1 x) ell1
  let a2 := normalizedMetricCovector (g2 y) ell2
  let M1 := metricOperatorField g1 x
  let M2 := metricOperatorField g2 y
  let G1 := coordinateConnectionField (inverseMetricField (metricOperatorField g1))
    (metricOperatorField g1) x
  let G2 := coordinateConnectionField (inverseMetricField (metricOperatorField g2))
    (metricOperatorField g2) y
  let G1' := coordinateConnectionField
    (inverseMetricField (metricOperatorField (fun z => c1 z • g1 z)))
    (metricOperatorField (fun z => c1 z • g1 z)) x
  let G2' := coordinateConnectionField
    (inverseMetricField (metricOperatorField (fun z => c2 z • g2 z)))
    (metricOperatorField (fun z => c2 z • g2 z)) y
  let H (A B : R3 →L[ℝ] R3 →L[ℝ] R3) (X Y : R3 × R3) :=
    fderiv ℝ (fderiv ℝ rho) (x,y) X Y - ell (A X.1 Y.1,B X.2 Y.2)
  have hSplit (X Y : R3) : ell (X,Y) = ell1 X + ell2 Y :=
    (ell.comp_inl_add_comp_inr (X,Y)).symm
  have hA1 : normalizedMetricCovector (c1 x • g1 x) ell1 = a1 :=
    normalizedMetricCovector_smul (g1 x) hgp1 ell1 (c1 x) hcx.ne'
  have hA2 : normalizedMetricCovector (c2 y • g2 y) ell2 = a2 :=
    normalizedMetricCovector_smul (g2 y) hgp2 ell2 (c2 y) hcy.ne'
  have hM1 : metricOperatorField (fun z => c1 z • g1 z) x = c1 x • M1 :=
    map_smul matrixOperatorMap (c1 x) (g1 x)
  have hM2 : metricOperatorField (fun z => c2 z • g2 z) y = c2 y • M2 :=
    map_smul matrixOperatorMap (c2 y) (g2 y)
  have hOr1 (v : R3) : ⟪(c1 x • M1) v,a1⟫_ℝ = 0 ↔ ⟪M1 v,a1⟫_ℝ = 0 := by
    simp only [ContinuousLinearMap.smul_apply,real_inner_smul_left,mul_eq_zero,hcx.ne',false_or]
  have hOr2 (v : R3) : ⟪(c2 y • M2) v,a2⟫_ℝ = 0 ↔ ⟪M2 v,a2⟫_ℝ = 0 := by
    simp only [ContinuousLinearMap.smul_apply,real_inner_smul_left,mul_eq_zero,hcy.ne',false_or]
  have hEq1 (v : R3) :
      ⟪(c1 x • M1) v,v⟫_ℝ = ⟪(c1 x • M1) a1,a1⟫_ℝ ↔
        ⟪M1 v,v⟫_ℝ = ⟪M1 a1,a1⟫_ℝ := by
    simp only [ContinuousLinearMap.smul_apply,real_inner_smul_left]
    constructor
    · exact mul_left_cancel₀ hcx.ne'
    · intro h;rw [h]
  have hEq2 (v : R3) :
      ⟪(c2 y • M2) v,v⟫_ℝ = ⟪(c2 y • M2) a2,a2⟫_ℝ ↔
        ⟪M2 v,v⟫_ℝ = ⟪M2 a2,a2⟫_ℝ := by
    simp only [ContinuousLinearMap.smul_apply,real_inner_smul_left]
    constructor
    · exact mul_left_cancel₀ hcy.ne'
    · intro h;rw [h]
  have hSum (he1 : ell1 ≠ 0) (he2 : ell2 ≠ 0) (v1 v2 : R3)
      (ho1 : ⟪M1 v1,a1⟫_ℝ = 0) (heq1 : ⟪M1 v1,v1⟫_ℝ = ⟪M1 a1,a1⟫_ℝ)
      (ho2 : ⟪M2 v2,a2⟫_ℝ = 0) (heq2 : ⟪M2 v2,v2⟫_ℝ = ⟪M2 a2,a2⟫_ℝ) :
      H G1' G2' (a1,-a2) (a1,-a2) + H G1' G2' (v1,v2) (v1,v2) =
        H G1 G2 (a1,-a2) (a1,-a2) + H G1 G2 (v1,v2) (v1,v2) := by
    have h1 := native_metric_characteristic_connection_cancellation g1 c1 x hgd1 hgp1
      (fderiv ℝ c1 x) ell1 hc1.hasFDerivAt hcx he1 v1 ho1 heq1
    have h2 := native_metric_characteristic_connection_cancellation g2 c2 y hgd2 hgp2
      (fderiv ℝ c2 y) ell2 hc2.hasFDerivAt hcy he2 v2 ho2 heq2
    change ell1 (G1' a1 a1) + ell1 (G1' v1 v1) =
      ell1 (G1 a1 a1) + ell1 (G1 v1 v1) at h1
    change ell2 (G2' a2 a2) + ell2 (G2' v2 v2) =
      ell2 (G2 a2 a2) + ell2 (G2 v2 v2) at h2
    simp only [H,Prod.fst,Prod.snd,map_neg,ContinuousLinearMap.neg_apply,neg_neg,hSplit]
    linarith only [h1,h2]
  change
    (ell1 ≠ 0 ∧ ell2 ≠ 0 ∧ ∀ v1 v2 : R3,
      ⟪metricOperatorField (fun z => c1 z • g1 z) x v1,
        normalizedMetricCovector (c1 x • g1 x) ell1⟫_ℝ = 0 →
      ⟪metricOperatorField (fun z => c1 z • g1 z) x v1,v1⟫_ℝ =
        ⟪metricOperatorField (fun z => c1 z • g1 z) x
          (normalizedMetricCovector (c1 x • g1 x) ell1),
          normalizedMetricCovector (c1 x • g1 x) ell1⟫_ℝ →
      ⟪metricOperatorField (fun z => c2 z • g2 z) y v2,
        normalizedMetricCovector (c2 y • g2 y) ell2⟫_ℝ = 0 →
      ⟪metricOperatorField (fun z => c2 z • g2 z) y v2,v2⟫_ℝ =
        ⟪metricOperatorField (fun z => c2 z • g2 z) y
          (normalizedMetricCovector (c2 y • g2 y) ell2),
          normalizedMetricCovector (c2 y • g2 y) ell2⟫_ℝ →
      0 < H G1' G2' (normalizedMetricCovector (c1 x • g1 x) ell1,
          -normalizedMetricCovector (c2 y • g2 y) ell2)
        (normalizedMetricCovector (c1 x • g1 x) ell1,
          -normalizedMetricCovector (c2 y • g2 y) ell2) + H G1' G2' (v1,v2) (v1,v2)) ↔
    (ell1 ≠ 0 ∧ ell2 ≠ 0 ∧ ∀ v1 v2 : R3,
      ⟪M1 v1,a1⟫_ℝ = 0 → ⟪M1 v1,v1⟫_ℝ = ⟪M1 a1,a1⟫_ℝ →
      ⟪M2 v2,a2⟫_ℝ = 0 → ⟪M2 v2,v2⟫_ℝ = ⟪M2 a2,a2⟫_ℝ →
      0 < H G1 G2 (a1,-a2) (a1,-a2) + H G1 G2 (v1,v2) (v1,v2))
  simp only [hA1,hA2,hM1,hM2,hOr1,hOr2,hEq1,hEq2]
  constructor
  · rintro ⟨he1,he2,ht⟩
    refine ⟨he1,he2,fun v1 v2 ho1 heq1 ho2 heq2 => ?_⟩
    rw [← hSum he1 he2 v1 v2 ho1 heq1 ho2 heq2]
    exact ht v1 v2 ho1 heq1 ho2 heq2
  · rintro ⟨he1,he2,ht⟩
    refine ⟨he1,he2,fun v1 v2 ho1 heq1 ho2 heq2 => ?_⟩
    rw [hSum he1 he2 v1 v2 ho1 heq1 ho2 heq2]
    exact ht v1 v2 ho1 heq1 ho2 heq2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
