import Calderon.ActualHigherSZeroCommutatorNativeCoefficients
import Calderon.ActualHigherSScalarCommutatorNativeForm
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroScalarNativeForm
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  PrincipalCommutator ActualScalarPrincipalAdjoint PerturbedDensityAdjoint ActualHigherSFirstCoefficientJets
  ActualHigherSScalarCommutatorCoefficients ActualHigherSZeroScalarCommutatorForm
  ActualHigherSZeroCommutatorNativeCoefficients ActualHigherSScalarCommutatorNativeForm
  ActualHigherSScalarCommutatorForm
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def negDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] negDualNormed
@[instance_reducible] private def negDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] negDualSpace
@[instance_reducible] private def nativeZeroNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] nativeZeroNormed
@[instance_reducible] private def nativeZeroSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] nativeZeroSpace
section InputEnergy
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
local notation "U" => ActualHigherSFormation.higherSInput hO hD
lemma highInput_eq_zero_off (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hx : x ∉ tsupport F.val) : U F x = 0 := by
  have hr := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F
  exact image_eq_zero_of_notMem_tsupport (fun ht => hx (hr.2.2.1 ht))

/-- Exact high-mass/included-gradient energy against the original finite-core reference energy. -/
theorem exists_highInput_inclusion_reference_integral_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ δr Ar : ℝ, ∀ p : ℕ,
      0 < δr → 0 < Ar → 1 ≤ p → ∀ F : smoothCompactFiniteSphereCore hO hD,
      (tsupport F.val ⊆ K) →
      (∀ x ∈ tsupport F.val, 1 ≤ actualReferenceBeta g L q δr Ar p x) →
      inclusionEnergy IH (fun x => referenceDensityFamily g L (q,x))
        (actualReferenceBeta g L q δr Ar p) (U F) ≤
        Cr*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q δr Ar p x) F x := by
  obtain ⟨Cr,hCr,hcap⟩ := exists_finiteCoreSourceEnergy_uniform_reference_profile_bound hO hD g hg L K hK
  refine ⟨Cr,hCr,?_⟩
  intro q hq δr Ar p hδr hAr hp F hsub hbeta
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let beta := actualReferenceBeta g L q δr Ar p
  let u := U F
  have hmu : ∀ x, 0 ≤ mu x := fun x => (referenceDensityFamily_pos g hg L (q,x)).le
  have hm : Continuous mu := (contDiff_referenceDensityFamily g hg L).continuous.comp
    (continuous_const.prodMk continuous_id)
  have hb := continuous_actualReferenceBeta g hg L q δr Ar p hL hδr hAr
  have hbpos := actualReferenceBeta_pos g hg L q δr Ar p hL hδr hAr hp
  have hu : ContDiff ℝ ∞ u := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have h0 : ∀ x ∉ tsupport F.val, u x = 0 := highInput_eq_zero_off hO hD F
  have hEi := inclusionEnergy_integrable IH mu beta u (tsupport F.val) F.property.2.1
    hm hb (fun x => (hbpos x).ne') hu h0
  have hNi := ActualFiniteHarmonicModel.integrable_finiteCoreReferenceProfileEnergy hO hD
    g hg L q beta hb hbpos F
  have hPt : ∀ x, mu x*inclusionEnergyDensity IH (beta x) u x ≤
      Cr*(mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F x) := by
    intro x
    by_cases hx : x ∈ tsupport F.val
    · have hs : inclusionEnergyDensity IH (beta x) u x ≤ finiteCoreSourceEnergy hO hD (beta x) F x :=
        native_threeHalf_angular_energy_le_finiteCoreSourceEnergy hO hD (beta x) F x
      have hc := hs.trans (hcap q hq x (hsub hx) (beta x) (hbeta x hx) F)
      exact (mul_le_mul_of_nonneg_left hc (hmu x)).trans_eq (by ring)
    · have hd0 (i : Fin 3) := directional_eq_zero_off u (tsupport F.val)
        (isClosed_tsupport F.val) h0 (coordinateDirection i) x hx
      have hz : inclusionEnergyDensity IH (beta x) u x = 0 := by
        simp only [inclusionEnergyDensity,h0 x hx,hd0,map_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),
          Finset.sum_const_zero,mul_zero,add_zero]
      rw [hz,mul_zero]
      exact mul_nonneg hCr.le (mul_nonneg (hmu x)
        (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta x) (hbpos x).le F x))
  have hi := integral_mono hEi (hNi.const_mul Cr) hPt
  rw [integral_const_mul] at hi
  exact hi
end InputEnergy

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZc" => ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "BETA" => actualReferenceBeta g L
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

/-- The actual canonical zero-base S / actual scalar-principal composed negative commutator. -/
def nativeScalarZeroCommutator (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (h : MatrixField) (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) : Neg :=
  scalarZeroCoordinateCommutatorSum
    (fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j)
    (fun y => CZc g2 δr Ar p q y) (ActualHigherSFormation.higherSInput hO hD F0) x
local notation "NC" => nativeScalarZeroCommutator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact native form task with original perturbation and profile hypotheses, before all angular inputs. -/
def ActualScalarZeroFormBound (δ : ℝ) (g2 : MatrixField) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ,
    0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
    (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
    ∀ F0 : smoothCompactFiniteSphereCore hO hD,
      (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
      (∀ x ∈ TS F0, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps*referenceRadius δr Ar p L x)) →
      (∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x) →
      (∀ x ∈ TS F0, referenceRadius δr Ar p L x*(BETA q δr Ar p x)^2 ≤ eps) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        sphereSobolevDualPairing (1/2 : ℝ) (halfInput hO hD F0 x) (NC g2 δr Ar p q h F0 x)) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F0 x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*
        sphereSobolevDualPairing (1/2 : ℝ) (halfInput hO hD F0 x) (NC g2 δr Ar p q h F0 x)| ≤
        K*eps*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F0 x
local notation "NativeForm" => ActualScalarZeroFormBound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Fixed native room: K after g2 and before every profile, perturbation and finite input. -/
theorem exists_actual_scalar_zero_commutator_reference_form
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) : NativeForm δ g2 := by
  obtain ⟨M,hM,hmuCap⟩ := exists_density_coordinate_relative_bound g hg L
    (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨Cr,hCr,hEcap⟩ := exists_highInput_inclusion_reference_integral_bound hO hD g hg L hL
    (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨Q,hQ,hcap⟩ := exists_actual_scalar_zero_coordinate_commutator_coefficient_bounds
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2
  have hP : 0 ≤ ‖halfDualPairingL‖ := norm_nonneg halfDualPairingL
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  refine ⟨27*(‖halfDualPairingL‖+1)*Q*((M+1)*‖IH‖+2)*Cr,by positivity,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh F0 hTF hjet hbeta hsmall
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let beta := BETA q δr Ar p
  let u := ActualHigherSFormation.higherSInput hO hD F0
  let aa : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j
  let zz : R3 → (Hi →L[ℝ] Neg) := fun y => CZc g2 δr Ar p q y
  have hbcont := continuous_actualReferenceBeta g hg L q δr Ar p hL hδr hAr
  have hbpos := actualReferenceBeta_pos g hg L q δr Ar p hL hδr hAr hp
  have hK : IsCompact (TS F0) := F0.property.2.1
  have hu : ContDiff ℝ ∞ u := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hu0 : ∀ x ∉ TS F0, u x = 0 := highInput_eq_zero_off hO hD F0
  have hsub : TS F0 ⊆ closedBall y0 ρ := by
    intro x hx
    simpa only [ActualHigherSFormation.higherSParam] using (hTF x hx).1.2.1
  have hm : ContDiff ℝ ∞ mu := (contDiff_referenceDensityFamily g hg L).comp
    (contDiff_const.prodMk contDiff_id)
  have hmu : ∀ x, 0 ≤ mu x := fun x => (referenceDensityFamily_pos g hg L (q,x)).le
  have ha : ∀ i j, ContDiff ℝ ∞ (aa i j) :=
    ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh
  have hz : ∀ x ∈ TS F0, ContDiffAt ℝ ∞ zz x := by
    intro x hx
    exact ActualHigherSZeroCoefficientJets.contDiffAt_canonicalZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2
        δr Ar p hδr hAr q x (hTF x hx)
  have hCaps : ∀ x ∈ TS F0, ZeroCommutatorCoefficientBudget aa zz x eps 1 (beta x) Q := by
    intro x hx
    have hc := hcap δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh x
      (hTF x hx) (hjet x hx) (hbeta x hx) (hsmall x hx)
    have hr : 0 ≤ referenceRadius δr Ar p L x := (referenceRadius_pos δr Ar p L x hδr hAr).le
    have hb1 := hbeta x hx
    have hb2 : 1 ≤ (beta x)^2 := by nlinarith only [hb1]
    have hr1 : referenceRadius δr Ar p L x ≤ 1 := by
      have hs := (hsmall x hx).trans heps1
      have hn := mul_nonneg hr (sub_nonneg.mpr hb2)
      nlinarith only [hs,hn]
    exact zeroCommutatorCoefficientBudget_radius_le_one aa zz x eps _ (beta x) Q
      heps hQ.le hr1 (hbpos x).le hc
  have hB := scalar_zero_coordinate_commutator_sum_form_bound halfDualPairingL IH mu beta u aa zz
    (TS F0) hK hm hbcont hbpos hu hu0 ha hz Q M eps hQ.le hM0 heps
    hmu hbeta (fun k x hx => hmuCap q hq x (hsub hx) k) hCaps
  have hN := integrable_finiteCoreReferenceProfileEnergy hO hD g hg L q beta hbcont hbpos F0
  have hE := hEcap q hq δr Ar p hδr hAr hp F0 hsub hbeta
  have hNI : 0 ≤ ∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x :=
    integral_nonneg (fun x => mul_nonneg (hmu x)
      (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta x) (hbpos x).le F0 x))
  have hEq : (fun x => mu x*sphereSobolevDualPairing (1/2 : ℝ) (IH (u x)) (NC g2 δr Ar p q h F0 x)) =
      (fun x => mu x*halfDualPairingL (IH (u x)) (scalarZeroCoordinateCommutatorSum aa zz u x)) := by
    funext x
    rw [halfDualPairingL_apply]
    rfl
  have hOrigI : Integrable (fun x => mu x*sphereSobolevDualPairing (1/2 : ℝ)
      (IH (u x)) (NC g2 δr Ar p q h F0 x)) := hEq.symm ▸ hB.1
  refine ⟨hOrigI,hN,?_⟩
  have hIEq := congrArg (fun J : R3 → ℝ => ∫ x, J x) hEq
  calc
    _ = |∫ x, mu x*halfDualPairingL (IH (u x)) (scalarZeroCoordinateCommutatorSum aa zz u x)| := congrArg abs hIEq
    _ ≤ (27*‖halfDualPairingL‖*Q*((M+1)*‖IH‖+2)*eps)*inclusionEnergy IH mu beta u := hB.2
    _ ≤ (27*‖halfDualPairingL‖*Q*((M+1)*‖IH‖+2)*eps)*
        (Cr*∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ (27*(‖halfDualPairingL‖+1)*Q*((M+1)*‖IH‖+2)*Cr)*eps*
        (∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x) := by
      have hpos : 0 ≤ 27*Q*((M+1)*‖IH‖+2)*Cr*eps*
          (∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x) := by positivity
      nlinarith only [hpos]

/-- Same W and common room before g2, with actual native Jacobian guard retained. -/
theorem exists_retained_actual_scalar_zero_commutator_reference_form
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ _Cm : CRoom hreg δ0 W δ,
      (∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z) ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → NativeForm δ g2 := by
  obtain ⟨δ,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  refine ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,hJac,?_⟩
  intro g2 hg2
  exact exists_actual_scalar_zero_commutator_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroScalarNativeForm
