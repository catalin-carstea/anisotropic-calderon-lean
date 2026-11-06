import Calderon.ActualReferenceExponentialGauge
import Calderon.ActualReferenceRadialJets
import Calderon.NativeBoundaryCoefficientFamilies

/-! Full upfront: day-oct13/actual-gauge-boundary-jets-author-oct15-v001/EXPANSION.md.
SAME actual gauge and coefficient. Only q in Icc and the retained finite base domain.
No conormal, adjoint, divided Taylor, or coercivity conclusion is assumed. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap MetricVolume
  SphereHarmonic NativeBoundaryCoefficientFamilies

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)

def referenceGaugePrincipalCoefficient
    (a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (p : (ℝ × (R3 × ℝ)) × R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  referenceExponentialGauge g L Φ p.1 p.2 • a p

def referenceGaugeNormalCoefficient
    (a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ) :
    (ℝ × (R3 × ℝ)) × R3 → ℝ :=
  normalCoefficientFunction (referenceGaugePrincipalCoefficient g L Φ a)

def referenceGaugeTangentCoefficient
    (a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    (ℝ × (R3 × ℝ)) × R3 → ℝ :=
  tangentCoefficientFunction (referenceGaugePrincipalCoefficient g L Φ a) j

lemma hasDerivAt_matrix_entry
    (A : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (A' : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (hA : HasDerivAt A A' r)
    (i j : Fin 3) : HasDerivAt (fun t => A t i j) (A' i j) r := by
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) j

lemma hasDerivAt_normal_matrix_sum
    (A : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (A' : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (hA : HasDerivAt A A' r) (z : R3) :
    HasDerivAt (fun t => ∑ i : Fin 3, ∑ j : Fin 3, z i*A t i j*z j)
      (∑ i : Fin 3, ∑ j : Fin 3, z i*A' i j*z j) r := by
  apply HasDerivAt.fun_sum
  intro i hi
  apply HasDerivAt.fun_sum
  intro j hj
  exact ((hasDerivAt_matrix_entry A A' r hA i j).const_mul (z i)).mul_const (z j)

lemma hasDerivAt_row_matrix_sum
    (A : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (A' : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (hA : HasDerivAt A A' r)
    (z : R3) (j : Fin 3) :
    HasDerivAt (fun t => ∑ i : Fin 3, z i*A t i j)
      (∑ i : Fin 3, z i*A' i j) r := by
  apply HasDerivAt.fun_sum
  intro i hi
  exact (hasDerivAt_matrix_entry A A' r hA i j).const_mul (z i)

lemma row_matrix_sum_smul_one (k : ℝ) (z : R3) (j : Fin 3) :
    (∑ i : Fin 3, z i*(k • (1 : Matrix (Fin 3) (Fin 3) ℝ)) i j) = k*z j := by
  simp [Matrix.one_apply, Pi.smul_apply, smul_eq_mul, mul_ite, ite_mul, mul_comm]

lemma normal_matrix_sum_smul_one (k : ℝ) (x : UnitSphere) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      x.val i*(k • (1 : Matrix (Fin 3) (Fin 3) ℝ)) i j*x.val j) = k := by
  calc
    _ = ∑ i : Fin 3, x.val i*k*x.val i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Matrix.one_apply, Pi.smul_apply, smul_eq_mul, mul_ite, ite_mul]
    _ = k*(∑ i : Fin 3, (x.val i)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = k := by rw [unitSphere_sum_sq, mul_one]

variable (y0 : R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData

theorem referenceRescaledDepth_zero_radial_jet
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ)
    (z : R3) :
    referenceRescaledDepth g L Φ (q,(y,0)) z = conformalReferenceCoordinateDepth y ∧
    HasDerivAt (fun r : ℝ => referenceRescaledDepth g L Φ (q,(y,r)) z)
      (inner ℝ ((conformalReferenceGramFrameOperatorJoint g L (q,y)).adjoint
        (gradient conformalReferenceCoordinateDepth y)) z) 0 := by
  rcases hData.1 with ⟨hNormal,hρ,hρε,_,_,_,_,_,_,_,_,_,_,_,_⟩
  rcases hNormal with ⟨hEndpoint,hε,_,_,_,_,hGeom,_⟩
  rcases hEndpoint with ⟨_,_,_,_,_,_,_,_,hValue,hFirst,_⟩
  have hyε : ‖y-y0‖ ≤ ε := by linarith
  have hyB : (y,0) ∈ B := by
    simpa only [zero_smul] using
      (hGeom q hq y hyε 0 (by simpa using le_of_lt hε) 0 (by simp)).1
  let Θ : R3 × R3 → R3 := fun p => (Φ q p 1).1
  let F : R3 → R3 →L[ℝ] R3 := fun x => conformalReferenceGramFrameOperatorJoint g L (q,x)
  have hΘzero : Θ (y,0) = y := hValue q hq y hyB
  have hΘfirst : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ R3 R3+ContinuousLinearMap.snd ℝ R3 R3) (y,0) :=
    hFirst q hq y hyB
  have hCurve : HasDerivAt (fun r : ℝ => (y,r • F y z)) (0,F y z) 0 := by
    simpa only [HasDerivAt,HasDerivAtFilter,hasFDerivAtFilter_iff_isLittleOTVS,
      ContinuousLinearMap.toSpanSingleton_apply,Function.comp_def,id_eq,one_smul] using
      (hasDerivAt_const (0 : ℝ) y).prodMk
        ((hasDerivAt_id (0 : ℝ)).smul_const (F y z))
  have hΘcurve : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ R3 R3+ContinuousLinearMap.snd ℝ R3 R3)
      (y,(0 : ℝ) • F y z) := by
    simpa only [zero_smul] using hΘfirst
  have hX : HasDerivAt (fun r : ℝ => Θ (y,r • F y z)) (F y z) 0 := by
    have h := hΘcurve.comp_hasDerivAt 0 hCurve
    have hV : (ContinuousLinearMap.fst ℝ R3 R3+ContinuousLinearMap.snd ℝ R3 R3)
        (0,F y z) = F y z := by
      change (0 : R3)+F y z = F y z
      exact zero_add _
    rw [hV] at h
    simpa only [HasDerivAt,HasDerivAtFilter,hasFDerivAtFilter_iff_isLittleOTVS,
      ContinuousLinearMap.toSpanSingleton_apply,Function.comp_def] using h
  have ht : HasFDerivAt conformalReferenceCoordinateDepth
      (fderiv ℝ conformalReferenceCoordinateDepth y) (Θ (y,(0 : ℝ) • F y z)) := by
    simpa only [zero_smul,hΘzero] using
      (contDiff_conformalReferenceCoordinateDepth.differentiable (by simp) y).hasFDerivAt
  constructor
  · change conformalReferenceCoordinateDepth (Θ (y,(0 : ℝ) • F y z)) = _
    rw [zero_smul,hΘzero]
  · change HasDerivAt
      (fun r : ℝ => conformalReferenceCoordinateDepth (Θ (y,r • F y z)))
      (inner ℝ ((F y).adjoint (gradient conformalReferenceCoordinateDepth y)) z) 0
    simpa only [HasDerivAt,HasDerivAtFilter,hasFDerivAtFilter_iff_isLittleOTVS,
      ContinuousLinearMap.toSpanSingleton_apply,Function.comp_def,
      ContinuousLinearMap.adjoint_inner_left,inner_gradient_left,smul_eq_mul] using
      ht.comp_hasDerivAt 0 hX

theorem referenceExponentialGauge_zero_radial_jet
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ)
    (z : R3) :
    referenceExponentialGauge g L Φ (q,(y,0)) z = 1 ∧
    HasDerivAt (fun r : ℝ => referenceExponentialGauge g L Φ (q,(y,r)) z)
      (inner ℝ (referenceCenterDrift g L q y) z) 0 := by
  obtain ⟨ht0,ht⟩ := referenceRescaledDepth_zero_radial_jet
    g L Φ y0 B ε C ρ H a w hData q hq y hy z
  constructor
  · simp only [referenceExponentialGauge,ht0,sub_self,mul_zero,Real.exp_zero]
  · have hm := ((ht.sub_const (conformalReferenceCoordinateDepth y)).const_mul L).exp
    simpa only [referenceExponentialGauge,ht0,sub_self,mul_zero,Real.exp_zero,
      one_mul,referenceCenterDrift,real_inner_smul_left] using hm

theorem referenceGaugePrincipalCoefficient_zero_radial_jet
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ)
    (z : R3) (hz : ‖z‖ ≤ 2) :
    referenceGaugePrincipalCoefficient g L Φ a ((q,(y,0)),z) = 1 ∧
    HasDerivAt (fun r : ℝ => referenceGaugePrincipalCoefficient g L Φ a ((q,(y,r)),z))
      ((inner ℝ (referenceCenterDrift g L q y) z) •
        (1 : Matrix (Fin 3) (Fin 3) ℝ)) 0 := by
  obtain ⟨hm0,hm⟩ := referenceExponentialGauge_zero_radial_jet
    g L Φ y0 B ε C ρ H a w hData q hq y hy z
  have hc := jointReference_coefficient_zero_radial_jets
    g L y0 Φ B ε C ρ H a w hData q hq y hy z hz
  have ha0 := hc.2.1
  have ha := hc.2.2.2.2.1
  constructor
  · simp only [referenceGaugePrincipalCoefficient,hm0,ha0,one_smul]
  · apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    have haij := hasDerivAt_matrix_entry (fun r : ℝ => a ((q,(y,r)),z)) 0 0 ha i j
    simpa only [HasDerivAt,HasDerivAtFilter,hasFDerivAtFilter_iff_isLittleOTVS,
      ContinuousLinearMap.toSpanSingleton_apply,Function.comp_def,
      referenceGaugePrincipalCoefficient,hm0,ha0,Matrix.smul_apply,
      Pi.smul_apply',Pi.mul_apply,smul_eq_mul,Matrix.zero_apply,
      zero_mul,mul_zero,one_mul,zero_add,add_zero] using hm.mul haij

theorem referenceGaugeNormalCoefficient_zero_radial_jet
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ)
    (x : UnitSphere) :
    referenceGaugeNormalCoefficient g L Φ a ((q,(y,0)),x.val) = 1 ∧
    HasDerivAt (fun r : ℝ => referenceGaugeNormalCoefficient g L Φ a ((q,(y,r)),x.val))
      (inner ℝ (referenceCenterDrift g L q y) x.val) 0 := by
  have hx : ‖x.val‖ ≤ 2 := by
    rw [norm_eq_of_mem_sphere x]
    norm_num
  obtain ⟨hA0,hA⟩ := referenceGaugePrincipalCoefficient_zero_radial_jet
    g L Φ y0 B ε C ρ H a w hData q hq y hy x.val hx
  constructor
  · change (∑ i : Fin 3, ∑ j : Fin 3,
      x.val i*referenceGaugePrincipalCoefficient g L Φ a ((q,(y,0)),x.val) i j*x.val j) = 1
    rw [hA0]
    simpa only [one_smul] using normal_matrix_sum_smul_one 1 x
  · have hn := hasDerivAt_normal_matrix_sum
      (fun r : ℝ => referenceGaugePrincipalCoefficient g L Φ a ((q,(y,r)),x.val))
      ((inner ℝ (referenceCenterDrift g L q y) x.val) •
        (1 : Matrix (Fin 3) (Fin 3) ℝ)) 0 hA x.val
    rw [normal_matrix_sum_smul_one] at hn
    exact hn

theorem referenceGaugeTangentCoefficient_zero_radial_jet
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ)
    (x : UnitSphere) (j : Fin 3) :
    referenceGaugeTangentCoefficient g L Φ a j ((q,(y,0)),x.val) = 0 ∧
    HasDerivAt (fun r : ℝ => referenceGaugeTangentCoefficient g L Φ a j ((q,(y,r)),x.val))
      0 0 := by
  have hx : ‖x.val‖ ≤ 2 := by
    rw [norm_eq_of_mem_sphere x]
    norm_num
  obtain ⟨hA0,hA⟩ := referenceGaugePrincipalCoefficient_zero_radial_jet
    g L Φ y0 B ε C ρ H a w hData q hq y hy x.val hx
  obtain ⟨hn0,hn⟩ := referenceGaugeNormalCoefficient_zero_radial_jet
    g L Φ y0 B ε C ρ H a w hData q hq y hy x
  constructor
  · change (∑ i : Fin 3,
      x.val i*referenceGaugePrincipalCoefficient g L Φ a ((q,(y,0)),x.val) i j) -
      referenceGaugeNormalCoefficient g L Φ a ((q,(y,0)),x.val)*x.val j = 0
    rw [hA0,hn0]
    have hr := row_matrix_sum_smul_one 1 x.val j
    simp only [one_smul,one_mul] at hr
    rw [hr,one_mul,sub_self]
  · have hr := hasDerivAt_row_matrix_sum
      (fun r : ℝ => referenceGaugePrincipalCoefficient g L Φ a ((q,(y,r)),x.val))
      ((inner ℝ (referenceCenterDrift g L q y) x.val) •
        (1 : Matrix (Fin 3) (Fin 3) ℝ)) 0 hA x.val j
    rw [row_matrix_sum_smul_one] at hr
    simpa only [HasDerivAt,HasDerivAtFilter,hasFDerivAtFilter_iff_isLittleOTVS,
      ContinuousLinearMap.toSpanSingleton_apply,Function.comp_def,Pi.sub_apply,
      referenceGaugeTangentCoefficient,tangentCoefficientFunction,
      referenceGaugeNormalCoefficient,smul_eq_mul,sub_self] using hr.sub (hn.mul_const (x.val j))

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugePrincipalCoefficient
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalCoefficient
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeTangentCoefficient
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceRescaledDepth_zero_radial_jet
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceExponentialGauge_zero_radial_jet
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugePrincipalCoefficient_zero_radial_jet
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalCoefficient_zero_radial_jet
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeTangentCoefficient_zero_radial_jet

#print axioms OAI.AnisotropicCalderon.ConnectionError.hasDerivAt_matrix_entry
#print axioms OAI.AnisotropicCalderon.ConnectionError.hasDerivAt_normal_matrix_sum
#print axioms OAI.AnisotropicCalderon.ConnectionError.hasDerivAt_row_matrix_sum
#print axioms OAI.AnisotropicCalderon.ConnectionError.row_matrix_sum_smul_one
#print axioms OAI.AnisotropicCalderon.ConnectionError.normal_matrix_sum_smul_one
